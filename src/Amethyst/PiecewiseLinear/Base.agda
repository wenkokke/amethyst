--------------------------------------------------------------------------------
-- Amethyst: Neural Network Verification in Agda
--
-- This module contains an implementation of naive linearisation, which
-- approximates non-linear functions using piecewise-linear approximations,
-- i.e., with a sequence of connected line segments.
-- The function `linearise` approximates a function `f : Float →  Float` over
-- an interval `(lower, upper)` using `pieces` line segments:
--
--   1. We compute a step size `step` which divides the interval `(lower,
--      upper)` into `pieces` subintervals of size `step`.
--   2. For each sub-interval `(lowerᵢ, upperᵢ)`, where `upperᵢ` is `lowerᵢ +
--      step`, we pick the line segment `fᵢ(x) = mᵢ * x + bᵢ`, with slope `mᵢ`
--      and y-intercept `bᵢ`, from `(lowerᵢ, f(lowerᵢ))` to `(upperᵢ, f(upperᵢ))`.
--   3. Finally, we connect all line segments `fᵢ`. The result is a piecewise-
--      linear approximation for `f` over the interval `(lower, upper)`.
--
-- The number of segments determines the granularity of the approximation,
-- though the approximations do not necessarily becomes less precise with an
-- increased number of segments: e.g., for the exponential function and tanh,
-- we observe that approximations which use an odd number `pieces` outperform
-- approximations which use `pieces + 1` segments.
--
-- Exports:
--
--   - LineSegment (slope; intercept)
--   - LineSegments ([]; _∷_)
--   - PiecewiseLinearFn ([]; _∷_)
--   - OutOfBoundsStrategy (constant; nearest; extrapolate)
--   - linearise
--
-- NOTE: The module also exports the following definitions, but these should be
--       considered "package private", and should not be relied upon.
--
--   - head
--   - _+[_*_]
--   - last
--
--------------------------------------------------------------------------------
module Amethyst.PiecewiseLinear.Base where

open import Data.Bool as Bool using (Bool; true; false; if_then_else_)
open import Data.Float as Float using (Float; _+_; _-_; _*_; _÷_; _≤ᵇ_)
open import Data.Nat as Nat using (ℕ; suc; zero; pred; NonZero)
open import Data.Vec as Vec using (Vec)

-- |Repeated addition of floating-point numbers, by recursion on a natural number.
--
--  NOTE: The reason this is done by recusion on the natural `z`, instead of by just
--        evaluating the floating-point expression, is that (at the time of writing)
--        it's not possible to prove properties about floating-point arithmetic in
--        Agda. By recursing on a natural, we can construct exactly the structure
--        that arises from the LineSegments construction.
--
_+[_*_] : (x y : Float) (z : ℕ) → Float
x +[ y * zero  ] = x
x +[ y * suc z ] = (x + y) +[ y * z ]

-- |A line segment is defined by a lower and upper bound on the x-values, a slope,
--  and and intercept.
record LineSegment (lower upper : Float) : Set where
  field
    slope     : Float
    intercept : Float

-- |A sequence of contiguous line segments.
data LineSegments (lower step : Float) : (pieces : ℕ) → Set where
  []  : LineSegments lower step 0
  _∷_ : ∀ {pieces : ℕ}
        (ls : LineSegment lower (lower + step))
      → (pl : LineSegments (lower + step) step pieces)
      → LineSegments lower step (suc pieces)

-- |Different strategies for handling out of bounds values
-- How should a piecewise-linear approximation behave outside of the interval?
-- We have three simple options:
--
--   1. `constant`: specify a constant value
--   2. `extrapolate`: extrapolate the last line segment beyond the interval boundaries.
--   3. `nearest`: return the value of the nearest point within the extrapolated intervals
--
-- The second option is unsound, as it may result in cases where the codomain of
-- the piecewise-linear approximation is not a subset of the codomain of the
-- approximated function. For instance, the piecewise-linear approximation of
-- the exp-function may return values <0 for a sufficiently small input.
-- However, we have found that it works well in practice. The third option is
-- sound, albeit a bit crude.
data OutOfBoundsStrategy : Set where
  constant      : Float → OutOfBoundsStrategy
  extrapolate   : OutOfBoundsStrategy
  nearestValue  : OutOfBoundsStrategy

-- |A piecewise linear function
record PiecewiseLinearFn : Set where
  field
    lowerOOBStrat : OutOfBoundsStrategy
    {lower step}  : Float
    {pieces}      : ℕ
    .{{pieces≢0}} : NonZero pieces
    lineSegments  : LineSegments lower step pieces
    upperOOBStrat : OutOfBoundsStrategy
  
  upper : Float
  upper = lower +[ step * suc pieces ]


private
  variable
    pieces : ℕ
    lower  : Float
    step   : Float
    upper  : Float

-- |Return the first line segment in a piecewise-linear function.
first : .{{NonZero pieces}} → (pl : LineSegments lower step pieces)
      → LineSegment lower (lower + step)
first (l ∷ ls) = l

-- |Return the last line segment in a piecewise-linear function.
last : .{{NonZero pieces}} → (pl : LineSegments lower step pieces)
     → LineSegment (lower +[ step * (pred pieces) ]) (lower +[ step * pieces ])
last (l ∷ [])         = l
last (_ ∷ ls@(_ ∷ _)) = last ls

private
  -- |Approximate the function f between `lower` and `lower + step` using one line segment.
  lineSegment : (f : Float → Float) (lower step : Float) → LineSegment lower (lower + step)
  lineSegment f lower step =
    let upper     = lower + step
        slope     = (f upper - f lower) ÷ (upper - lower)
        intercept = f lower - (slope * lower)
    in record { slope = slope ; intercept = intercept }

  -- |Approximate the function f from lower, using line segments of length step.
  lineSegments : (f : Float → Float) (lower step : Float) (pieces : ℕ)
               → LineSegments lower step pieces
  lineSegments f lower step zero = []
  lineSegments f lower step (suc pieces) = lineSegment f lower step ∷ lineSegments f (lower + step) step pieces

-- |Approximate the function f between lower and upper using line segments.
linearise : (f : Float → Float) (lower upper : Float)
            (pieces : ℕ) → .{{NonZero pieces}}
          → (lowerOOB upperOOB : OutOfBoundsStrategy)
          → PiecewiseLinearFn
linearise f lower upper pieces@(suc _) lowerOOB upperOBB = record
  { lowerOOBStrat = lowerOOB
  ; lineSegments  = lineSegments f lower ((upper - lower) ÷ Float.fromℕ pieces) pieces
  ; upperOOBStrat = upperOBB
  }

