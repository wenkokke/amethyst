--------------------------------------------------------------------------------
-- Amethyst Models: Examples of Neural Network Verification in Agda
--
-- This module contains an example use of Amethyst, to verify the correctness of
-- a simple AND-gate network.
--------------------------------------------------------------------------------

{-# OPTIONS --allow-exec #-}

module AND-Gate-2-Sigmoid-1 where

open import Amethyst.Prelude
open import Data.Float using (Float)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

layer : Layer Float 2 1
layer = record
  { weights    = [ 5.0e1 ] ∷ [ 5.0e1 ] ∷ []
  ; biases     = [ -7.5e1 ]
  ; activation = sigmoid
  }

model : Network Float 2 1 1
model = layer ∷ []

-- Test some exact constraints

exactConstraints : NetworkConstraints 2 1
exactConstraints (i₀ ∷ i₁ ∷ []) (o₀ ∷ []) =
  (i₀ == 0·0f ∧ i₁ == 0·0f ⇒ o₀ == 0·0f) ∷
  (i₀ == 0·0f ∧ i₁ == 1·0f ⇒ o₀ == 0·0f) ∷
  (i₀ == 1·0f ∧ i₁ == 0·0f ⇒ o₀ == 0·0f) ∷
  (i₀ == 1·0f ∧ i₁ == 1·0f ⇒ o₀ == 1·0f) ∷
  []

_ : z3 (query model exactConstraints) ≡ unsat ∷ []
_ = refl

_ : evalNetwork model (0.0 ∷ 0.0 ∷ []) ≡ (0.0 ∷ [])
_ = refl
_ : evalNetwork model (0.0 ∷ 1.0 ∷ []) ≡ (0.0 ∷ [])
_ = refl
_ : evalNetwork model (1.0 ∷ 0.0 ∷ []) ≡ (0.0 ∷ [])
_ = refl
_ : evalNetwork model (1.0 ∷ 1.0 ∷ []) ≡ (1.0 ∷ [])
_ = refl

-- Test some more useful constraints

ε : ∀ {Γ} → Term Γ REAL
ε = toReal 0.2

truthy : ∀ {Γ} → Term Γ REAL → Term Γ BOOL
truthy x = ∣ 1·0f - x ∣ ≤ ε

falsey : ∀ {Γ} → Term Γ REAL → Term Γ BOOL
falsey x = ∣ 0·0f - x ∣ ≤ ε

fuzzyConstraints : NetworkConstraints 2 1
fuzzyConstraints (i₀ ∷ i₁ ∷ []) (o₀ ∷ []) =
  (falsey i₀ ∧ falsey i₁ ⇒ falsey o₀) ∷
  (falsey i₀ ∧ truthy i₁ ⇒ falsey o₀) ∷
  (truthy i₀ ∧ falsey i₁ ⇒ falsey o₀) ∷
  (truthy i₀ ∧ truthy i₁ ⇒ truthy o₀) ∷
  []

_ : z3 (query model fuzzyConstraints) ≡ unsat ∷ []
_ = refl
