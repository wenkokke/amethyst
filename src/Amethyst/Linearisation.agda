-- This module contains an implementation of linearisation.
--
-- Exports:
--
--   - LineSegment (slope; intercept)
--   - PiecewiseLinear ([]; _∷_)
--   - evalExtrap
--   - evalBounded
--   - linearise
--
module Amethyst.Linearisation where

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

private
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

  -- |Return the y-value corresponding to x on the line segment ls. If x is out of
  --  bounds, extrapolate the line segment.
  evalExtrapLineSegment : (ls : LineSegment lower upper) (x : Float) → Float
  evalExtrapLineSegment ls x = (x * slope) + intercept
    where
      open LineSegment ls using (slope; intercept)

  -- |Return the y-value corresponding to x on the line segment ls. If x is out of
  --  bounds, return the y-value corresponding to the x-value closest to x which is
  --  in bounds, i.e., either lower or upper.
  evalLineSegment : (ls : LineSegment lower upper) (x : Float) → Float
  evalLineSegment {lower} {upper} ls x =
    if x ≤ᵇ lower then evalExtrapLineSegment ls lower else
    if upper ≤ᵇ x then evalExtrapLineSegment ls upper else
    evalExtrapLineSegment ls x

  -- |Approximate the function f between lower and upper using one line segment.
  lineSegment : (f : Float → Float) (lower step : Float) → LineSegment lower (lower + step)
  lineSegment f lower step =
    let upper     = lower + step
        slope     = (f upper - f lower) ÷ (upper - lower)
        intercept = f lower - (slope * lower)
    in record { slope = slope ; intercept = intercept }

-- |Return the y-value corresponding to x on the piecewise-linear function.
--  If x is out of bounds, extrapolate the head/last line segment.
evalExtrap : (pl : PiecewiseLinear lower step (suc pieces)) (x : Float) → Float
evalExtrap {lower} {step} (ls ∷ [])         x = evalExtrapLineSegment ls x
evalExtrap {lower} {step} (ls ∷ pl@(_ ∷ _)) x =
  if x ≤ᵇ lower + step then evalExtrapLineSegment ls x else
  evalExtrap pl x

-- |Return the y-value corresponding to x on the piecewise-linear function.
--  If x is out of bounds, return the y-value corresponding to the x-value
--  closest to x which is in bounds, i.e., either lower or upper.
evalBounded : (pl : PiecewiseLinear lower step (suc pieces)) (x : Float) → Float
evalBounded {lower} {step} {pieces} pl x =
  let upper = lower +[ step * suc pieces ]
  in if x ≤ᵇ lower then evalExtrapLineSegment (head pl) x else
     if upper ≤ᵇ x then evalExtrapLineSegment (last pl) x else
     evalExtrap pl x

private
  -- |Approximate the function f from lower, using pieces line segments of length step.
  linearise′ : (f : Float → Float) (lower step : Float) (pieces : ℕ) → PiecewiseLinear lower step pieces
  linearise′ f lower step zero = []
  linearise′ f lower step (suc pieces) = lineSegment f lower step ∷ linearise′ f (lower + step) step pieces

-- |Approximate the function f between lower and upper using pieces line segments.
linearise : (f : Float → Float) (lower upper : Float) (pieces : ℕ)
          → PiecewiseLinear lower ((upper - lower) ÷ Float.fromℕ pieces) pieces
linearise f lower upper pieces = linearise′ f lower ((upper - lower) ÷ Float.fromℕ pieces) pieces

-- -}
-- -}
-- -}
-- -}
-- -}
