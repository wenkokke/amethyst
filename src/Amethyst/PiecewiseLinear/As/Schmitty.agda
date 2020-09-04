--------------------------------------------------------------------------------
-- Amethyst: Neural Network Verification in Agda
--
-- This module contains functions to reflect piecewise-linear functions to
-- Schmitty terms. The various reflections correspond to the various evaluations,
-- see `Amethyst.PiecewiseLinear.As.Float`.
--
-- Exports:
--
--  - reflectExtrap
--  - reflectBounded
--
--------------------------------------------------------------------------------
module Amethyst.PiecewiseLinear.As.Schmitty where

open import Amethyst.PiecewiseLinear.Base
open import Amethyst.LinearAlgebra.As.Schmitty
open import Data.Bool as Bool using (Bool; true; false; if_then_else_)
open import Data.Float as Float using (Float; _+_; _*_; _≤ᵇ_)
open import Data.Nat as Nat using (ℕ; suc; zero)
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
  reflectExtrapLineSegment : (ls : LineSegment lower upper) → Real Γ → Real Γ
  reflectExtrapLineSegment ls x = app₂ add (app₂ mul x (toReal slope)) (toReal intercept)
    where
      open LineSegment ls using (slope; intercept)

  -- |Return the y-value corresponding to x on the line segment ls. If x is out of
  --  bounds, return the y-value corresponding to the x-value closest to x which is
  --  in bounds, i.e., either lower or upper.
  reflectBoundedLineSegment : (ls : LineSegment lower upper) → Real Γ → Real Γ
  reflectBoundedLineSegment {lower} {upper} ls x
    = app₃ ite (app₂ leq x (toReal lower)) (reflectExtrapLineSegment ls (toReal lower))
    $ app₃ ite (app₂ leq (toReal upper) x) (reflectExtrapLineSegment ls (toReal upper))
    $ reflectExtrapLineSegment ls x

-- |Return the y-value corresponding to x on the piecewise-linear function.
--  If x is out of bounds, extrapolate the head/last line segment.
reflectExtrap : (pl : PiecewiseLinear lower step (suc pieces)) → Real Γ → Real Γ
reflectExtrap {lower} {step} (ls ∷ [])         x = reflectExtrapLineSegment ls x
reflectExtrap {lower} {step} (ls ∷ pl@(_ ∷ _)) x
  = app₃ ite (app₂ leq x (app₂ add (toReal lower) (toReal step))) (reflectExtrapLineSegment ls x)
  $ reflectExtrap pl x

-- |Return the y-value corresponding to x on the piecewise-linear function.
--  If x is out of bounds, return the y-value corresponding to the x-value
--  closest to x which is in bounds, i.e., either lower or upper.
reflectBounded : (pl : PiecewiseLinear lower step (suc pieces)) → Real Γ → Real Γ
reflectBounded {lower} {step} {pieces} pl x =
  let upper = lower +[ step * suc pieces ]
  in app₃ ite (app₂ leq x (toReal lower)) (reflectExtrapLineSegment (head pl) x)
   $ app₃ ite (app₂ leq (toReal upper) x) (reflectExtrapLineSegment (last pl) x)
   $ reflectExtrap pl x
