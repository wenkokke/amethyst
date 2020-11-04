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
open import Data.Bool.Base using (Bool)
open import Data.Nat.Base using (ℕ)
open import Data.List.Base as List public using (List; []; _∷_; _++_)
open import Data.Vec.Base as Vec public using (Vec; []; _∷_; [_])
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

query : ∀ {n} {ls : LayerSpec n} →
  (let inputs = ∣ ls ₀∣)
  (let outputs = ∣ ls ₙ∣)
  (let Γ = Reals inputs ++ Reals outputs)
  → Network Float ls
  → NetworkConstraints inputs outputs
  → Script [] Γ (SAT ∷ [])
query n c = withReflectedNetworkAsScript n
  (λ iv ov → processConstraints (c iv ov) ∷ check-sat ∷ [])

queryWithModel : ∀ {n} {ls : LayerSpec n}
  (let inputs = ∣ ls ₀∣)
  (let outputs = ∣ ls ₙ∣)
  (let Γ = Reals inputs ++ Reals outputs)
  → Network Float ls
  → NetworkConstraints inputs outputs
  → Script [] Γ (MODEL Γ ∷  [])
queryWithModel n c = withReflectedNetworkAsScript n
  (λ iv ov → processConstraints (c iv ov) ∷ get-model ∷ [])

--------------------------------------------------------------------------------
-- Boolean operators

private
  variable
    Γ : Ctxt

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

--------------------------------------------------------------------------------
-- Float constants

0·0f 1·0f : Real Γ
0·0f = lit (float 0.0)
1·0f = lit (float 1.0)

--------------------------------------------------------------------------------
-- Float operators and relations

infix 17 _-_
_-_ : Op₂ (Term Γ REAL)
_-_ = app₂ sub

∣_∣ : Op₁ (Term Γ REAL)
∣ x ∣ = app₃ ite (app₂ leq x 0·0f) (app₁ neg x) x

infix 14 _==_
_==_ : (x y : Real Γ) → Term Γ BOOL
_==_ = app₂ eq

infix 14 _≤_
_≤_ : (x y : Real Γ) → Term Γ BOOL
_≤_ = app₂ leq
