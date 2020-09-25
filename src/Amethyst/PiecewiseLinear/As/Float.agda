--------------------------------------------------------------------------------
-- Amethyst: Neural Network Verification in Agda
--
-- This module contains functions to evaluate piecewise-linear functions as
-- functions on floating-point numbers.
-- Piecewise-linear approximations are built over an interval `(lower, upper)`.
--
-- Exports:
--
--   - eval
--
--------------------------------------------------------------------------------
module Amethyst.PiecewiseLinear.As.Float where

open import Amethyst.PiecewiseLinear.Base
open import Data.Bool as Bool using (Bool; true; false; if_then_else_; not)
open import Data.Float as Float using (Float; _+_; _*_; _≤ᵇ_)
open import Data.Nat as Nat using (ℕ; suc; zero; NonZero)
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
  evalLineSegment : (ls : LineSegment lower upper) (x : Float) → Float
  evalLineSegment ls x = (x * slope) + intercept
    where open LineSegment ls using (slope; intercept)

  -- |Return the y-value corresponding to x on the piecewise-linear function.
  --  If x is out of bounds, extrapolate the head/last line segment.
  evalLineSegments : .{{NonZero pieces}} → (pl : LineSegments lower step pieces) → Float → Float
  evalLineSegments {_} {lower} {step} (ls ∷ [])         x = evalLineSegment ls x
  evalLineSegments {_} {lower} {step} (ls ∷ pl@(_ ∷ _)) x =
    if x ≤ᵇ lower + step then evalLineSegment ls x else
    evalLineSegments pl x

  -- |Return the y-value corresponding to an out-of-bounds x value,
  -- given a strategy, the last line segment, and whether it's below or above the line segment 
  evalOutOfBoundsStrat : OutOfBoundsStrategy → LineSegment lower upper → Bool → Float → Float
  evalOutOfBoundsStrat {_}     {_}     (constant c) _  _     _ = c
  evalOutOfBoundsStrat {_}     {_}     extrapolate  ls _     x = evalLineSegment ls x
  evalOutOfBoundsStrat {lower} {upper} nearestValue ls below x = evalLineSegment ls (if below then lower else upper)

eval : PiecewiseLinearFn → Float → Float
eval f x = let module F = PiecewiseLinearFn f in
  if x ≤ᵇ F.lower  then
    evalOutOfBoundsStrat F.lowerOOBStrat (first F.lineSegments) true x
  else if F.upper ≤ᵇ x then
    evalOutOfBoundsStrat F.upperOOBStrat (last F.lineSegments) false x
  else
    evalLineSegments F.lineSegments x
