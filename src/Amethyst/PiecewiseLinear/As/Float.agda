-- This module contains functions to evaluate piecewise-linear functions as functions on floating-point
--
-- Exports:
--
--   - evalExtrap
--   - evalBounded
--
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
