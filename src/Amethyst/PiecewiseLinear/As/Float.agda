--------------------------------------------------------------------------------
-- Amethyst: Neural Network Verification in Agda
--
-- This module contains functions to evaluate piecewise-linear functions as
-- functions on floating-point numbers.
-- Piecewise-linear approximations are built over an interval `(lower, upper)`.
-- How should a piecewise-linear approximation behave outside of this interval?
-- We have three simple options:
--
--   1. We can extrapolate the first and last line segments beyond the interval
--      boundaries. This is implemented as `evalExtrap`.
--   2. We can return the minimum point, `f(lower)`, for inputs below the
--      interval, and return the maximum point, `f(upper)`, for inputs above the
--      interval. This is implemented as `evalBounded`.
--   3. We can combine (1) and (2). We start by extrapolating, following (1),
--      and allow the user to specify lower and upper bounds, where we switch to
--      returning the constant minimum and maximum, following (2). This is not
--      currently implemented.
--
-- The first option is unsound, as it may result in cases where the codomain of
-- the piecewise-linear approximation is not a subset of the codomain of the
-- approximated function. For instance, the piecewise-linear approximation of
-- the exp-function may return values <0 for a sufficiently small input.
-- However, we have found that it works well in practice. The second option is
-- sound, albeit a bit crude. The third option combines the best of (1) and (2),
-- but requires manual tweaking.
--
-- Exports:
--
--   - evalExtrap
--   - evalBounded
--
--------------------------------------------------------------------------------
module Amethyst.PiecewiseLinear.As.Float where

open import Amethyst.PiecewiseLinear.Base using (PiecewiseLinear; []; _∷_; LineSegment; head; _+[_*_]; last)
open import Data.Bool as Bool using (Bool; true; false; if_then_else_)
open import Data.Float as Float using (Float; _+_; _*_; _≤ᵇ_)
open import Data.Nat as Nat using (ℕ; suc; zero)
open import Data.Vec as Vec using (Vec)

private
  variable
    pieces : ℕ
    lower  : Float
    step   : Float
    upper  : Float

private
  -- |Return the y-value corresponding to x on the line segment ls. If x is out of
  --  bounds, extrapolate the line segment.
  evalExtrapLineSegment : (ls : LineSegment lower upper) (x : Float) → Float
  evalExtrapLineSegment ls x = (x * slope) + intercept
    where
      open LineSegment ls using (slope; intercept)

  -- |Return the y-value corresponding to x on the line segment ls. If x is out of
  --  bounds, return the y-value corresponding to the x-value closest to x which is
  --  in bounds, i.e., either lower or upper.
  evalBoundedLineSegment : (ls : LineSegment lower upper) → Float → Float
  evalBoundedLineSegment {lower} {upper} ls x =
    if x ≤ᵇ lower then evalExtrapLineSegment ls lower else
    if upper ≤ᵇ x then evalExtrapLineSegment ls upper else
    evalExtrapLineSegment ls x

-- |Return the y-value corresponding to x on the piecewise-linear function.
--  If x is out of bounds, extrapolate the head/last line segment.
evalExtrap : (pl : PiecewiseLinear lower step (suc pieces)) → Float → Float
evalExtrap {lower} {step} (ls ∷ [])         x = evalExtrapLineSegment ls x
evalExtrap {lower} {step} (ls ∷ pl@(_ ∷ _)) x =
  if x ≤ᵇ lower + step then evalExtrapLineSegment ls x else
  evalExtrap pl x

-- |Return the y-value corresponding to x on the piecewise-linear function.
--  If x is out of bounds, return the y-value corresponding to the x-value
--  closest to x which is in bounds, i.e., either lower or upper.
evalBounded : (pl : PiecewiseLinear lower step (suc pieces)) → Float → Float
evalBounded {lower} {step} {pieces} pl x =
  let upper = lower +[ step * suc pieces ]
  in if x ≤ᵇ lower then evalExtrapLineSegment (head pl) x else
     if upper ≤ᵇ x then evalExtrapLineSegment (last pl) x else
     evalExtrap pl x
