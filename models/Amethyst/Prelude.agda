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

open import Algebra.Core using (Op₁; Op₂)
open import Data.Bool using (Bool)
open import Data.Nat using (ℕ)
open import Data.List as List public using (List; []; _∷_; _++_)
open import Data.Vec as Vec public using (Vec; []; _∷_; [_])
open import Data.Float using (Float)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import SMT.Theories.Reals as Reals

open import Amethyst.Network public
open import Amethyst.LinearAlgebra.As.Schmitty public

open import SMT.Backend.Z3 Reals.reflectable public using (z3)
open import SMT.Backend.CVC4 Reals.reflectable public using (cvc4)

--------------------------------------------------------------------------------
-- Helper methods for generating constraints and queries

NetworkConstraints : ℕ → ℕ → Set
NetworkConstraints inputs outputs =
  Vec (Real Γ) inputs →
  Vec (Real Γ) outputs →
  List (Term Γ BOOL)
  where Γ = Reals inputs ++ Reals outputs

processConstraints : ∀ {Γ} → List (Term Γ BOOL) → Command Γ [] []
processConstraints constraints = assert (app₁ not (List.foldr (app₂ and) (app₀ true) constraints))

query : ∀ {inputs outputs layers} (let Γ = Reals inputs ++ Reals outputs)
  → Network Float inputs outputs layers
  → NetworkConstraints inputs outputs
  → Script [] Γ (SAT ∷ [])
query n c = withReflectedNetworkAsScript n
  (λ iv ov → processConstraints (c iv ov) ∷ check-sat ∷ [])

--------------------------------------------------------------------------------
-- Constants

private
  variable
    Γ : Ctxt

0·0f 1·0f : Real Γ
0·0f = lit (float 0.0)
1·0f = lit (float 1.0)

--------------------------------------------------------------------------------
-- Operators

infixr 3 _⇒_
_⇒_ : Op₂ (Term Γ BOOL)
_⇒_ = app₂ implies

infix 6 _∧_
_∧_ : Op₂ (Term Γ BOOL)
_∧_ = app₂ and

infix 5 _∨_
_∨_ : Op₂ (Term Γ BOOL)
_∨_ = app₂ or

infix 8 ¬_
¬_ : Op₁ (Term Γ BOOL)
¬_ = app₁ not

infix 7 _-_
_-_ : Op₂ (Term Γ REAL)
_-_ = app₂ sub

infix 4 _==_
_==_ : (x y : Real Γ) → Term Γ BOOL
_==_ = app₂ eq

infix 4 _≤_
_≤_ : (x y : Real Γ) → Term Γ BOOL
_≤_ = app₂ leq



