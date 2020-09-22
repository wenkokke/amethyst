--------------------------------------------------------------------------------
-- Amethyst Models: Examples of Neural Network Verification in Agda
--
-- This module exports a prelude of definitions often used in writing
-- verification conditions.
--
-- Exports:
--
--   - _⇒_
--   - _∧_
--   - _==_
--   - 0·0f
--   - 1·0f
--
--------------------------------------------------------------------------------
module Amethyst.Prelude where

open import Amethyst.Network public
open import Amethyst.LinearAlgebra.As.Schmitty public
open import Data.List as List public using (List; []; _∷_; _++_)
open import Data.Vec as Vec public using (Vec; []; _∷_; [_])
open import SMT.Theories.Reals as Reals
open import SMT.Backend.Z3 Reals.reflectable public using (z3)
open import SMT.Backend.CVC4 Reals.reflectable public using (cvc4)

private
  variable
    Γ : Ctxt

_⇒_ _∧_ : (a b : Term Γ BOOL) → Term Γ BOOL
_⇒_ = app₂ implies
_∧_ = app₂ and

_==_ : (x y : Real Γ) → Term Γ BOOL
_==_ = app₂ eq

0·0f 1·0f : Real Γ
0·0f = lit (float 0.0)
1·0f = lit (float 1.0)
