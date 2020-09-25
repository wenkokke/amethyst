--------------------------------------------------------------------------------
-- Amethyst: Neural Network Verification in Agda
--
-- This module contains functions to reflect piecewise-linear functions to
-- Schmitty terms. The various reflections correspond to the various evaluations,
-- see `Amethyst.PiecewiseLinear.As.Float`.
--
-- Exports:
--
--  - reflect
--
--------------------------------------------------------------------------------
module Amethyst.PiecewiseLinear.As.Schmitty where

open import Amethyst.PiecewiseLinear.Base
open import Amethyst.LinearAlgebra.As.Schmitty hiding (true; false)
open import Data.Bool as Bool using (Bool; true; false; if_then_else_)
open import Data.Float as Float using (Float; _+_; _*_; _≤ᵇ_)
open import Data.Nat as Nat using (ℕ; suc; zero; NonZero)
open import Data.Vec as Vec using (Vec)
open import Function using (_$_)

private
  variable
    Γ      : Ctxt
    pieces : ℕ
    lower  : Float
    step   : Float
    upper  : Float

private
  -- |Return the y-value corresponding to x on the line segment ls. If x is out of
  --  bounds, extrapolate the line segment.
  reflectLineSegment : (ls : LineSegment lower upper) → Real Γ → Real Γ
  reflectLineSegment ls x = app₂ add (app₂ mul x (toReal slope)) (toReal intercept)
    where open LineSegment ls using (slope; intercept)

  -- |Return the y-value corresponding to x on the piecewise-linear function.
  --  If x is out of bounds, extrapolate the head/last line segment.
  reflectLineSegments : .{{NonZero pieces}} → (pl : LineSegments lower step pieces) → Real Γ → Real Γ
  reflectLineSegments {_} {lower} {step} (ls ∷ [])         x = reflectLineSegment ls x
  reflectLineSegments {_} {lower} {step} (ls ∷ pl@(_ ∷ _)) x
    = app₃ ite (app₂ leq x (app₂ add (toReal lower) (toReal step))) (reflectLineSegment ls x)
    $ reflectLineSegments pl x

  -- |Return the y-value corresponding to an out-of-bounds x value,
  -- given a strategy, the last line segment, and whether it's below or above the line segment 
  reflectOutOfBoundsStrat : OutOfBoundsStrategy → LineSegment lower upper → Bool → Real Γ → Real Γ
  reflectOutOfBoundsStrat {_}     {_}     (constant c) _  _     _ = toReal c
  reflectOutOfBoundsStrat {_}     {_}     extrapolate  ls _     x = reflectLineSegment ls x
  reflectOutOfBoundsStrat {lower} {upper} nearestValue ls below x = reflectLineSegment ls (toReal v)
    where v = if below then lower else upper

-- |Return the y-value corresponding to x on the piecewise-linear function.
reflect : PiecewiseLinearFn → Real Γ → Real Γ
reflect f x = let module F = PiecewiseLinearFn f in
    app₃ ite (app₂ leq x (toReal F.lower)) (reflectOutOfBoundsStrat F.lowerOOBStrat (first F.lineSegments) true x)
  $ app₃ ite (app₂ leq (toReal F.upper) x) (reflectOutOfBoundsStrat F.upperOOBStrat (first F.lineSegments) false x)
  $ reflectLineSegments F.lineSegments x
