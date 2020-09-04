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
--   - PiecewiseLinear ([]; _∷_)
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
open import Data.Nat as Nat using (ℕ; suc; zero)
open import Data.Vec as Vec using (Vec)

private
  variable
    pieces : ℕ
    lower  : Float
    step   : Float
    upper  : Float

-- |A line segment is defined by a lower and upper bound on the x-values, a slope,
--  and and intercept.
record LineSegment (lower upper : Float) : Set where
  field
    slope     : Float
    intercept : Float

-- |A piecewise-linear function is a sequence of line segments.
data PiecewiseLinear (lower step : Float) : (pieces : ℕ) → Set where
  []  : PiecewiseLinear lower step 0
  _∷_ : (ls : LineSegment lower (lower + step))
      → (pl : PiecewiseLinear (lower + step) step pieces)
      → PiecewiseLinear lower step (suc pieces)

-- |Return the first line segment in a piecewise-linear function.
head : (pl : PiecewiseLinear lower step (suc pieces))
     → LineSegment lower (lower + step)
head (l ∷ ls) = l

-- |Repeated addition of floating-point numbers, by recursion on a natural number.
--
--  NOTE: The reason this is done by recusion on the natural `z`, instead of by just
--        evaluating the floating-point expression, is that (at the time of writing)
--        it's not possible to prove properties about floating-point arithmetic in
--        Agda. By recursing on a natural, we can construct exactly the structure
--        that arises from the PiecewiseLinear construction.
--
_+[_*_] : (x y : Float) (z : ℕ) → Float
x +[ y * zero  ] = x
x +[ y * suc z ] = (x + y) +[ y * z ]

-- |Return the last line segment in a piecewise-linear function.
last : (pl : PiecewiseLinear lower step (suc pieces))
     → LineSegment (lower +[ step * pieces ]) (lower +[ step * suc pieces ])
last (l ∷ [])         = l
last (_ ∷ ls@(_ ∷ _)) = last ls

private
  -- |Approximate the function f between lower and upper using one line segment.
  lineSegment : (f : Float → Float) (lower step : Float) → LineSegment lower (lower + step)
  lineSegment f lower step =
    let upper     = lower + step
        slope     = (f upper - f lower) ÷ (upper - lower)
        intercept = f lower - (slope * lower)
    in record { slope = slope ; intercept = intercept }

  -- |Approximate the function f from lower, using pieces line segments of length step.
  piecewiseLinear : (f : Float → Float) (lower step : Float) (pieces : ℕ) → PiecewiseLinear lower step pieces
  piecewiseLinear f lower step zero = []
  piecewiseLinear f lower step (suc pieces) = lineSegment f lower step ∷ piecewiseLinear f (lower + step) step pieces

-- |Approximate the function f between lower and upper using pieces line segments.
linearise : (f : Float → Float) (lower upper : Float) (pieces : ℕ)
          → PiecewiseLinear lower ((upper - lower) ÷ Float.fromℕ pieces) pieces
linearise f lower upper pieces = piecewiseLinear f lower ((upper - lower) ÷ Float.fromℕ pieces) pieces

-- -}
-- -}
-- -}
-- -}
-- -}
