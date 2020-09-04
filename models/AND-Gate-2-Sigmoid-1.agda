--------------------------------------------------------------------------------
-- Amethyst Models: Examples of Neural Network Verification in Agda
--
-- This module contains an example use of Amethyst, to verify the correctness of
-- a simple AND-gate network.
--------------------------------------------------------------------------------

{-# OPTIONS --allow-exec #-}

module AND-Gate-2-Sigmoid-1 where

open import Amethyst.Prelude
open import Data.Float
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

layer : Layer Float 2 1
layer = record
  { weights    = [ 5.0e8 ]
               ∷ [ 5.0e8 ]
               ∷ []
  ; biases     = [ -7.5e8 ]
  ; activation = sigmoid
  }

model : Network Float 2 1 1
model = layer ∷ []

script : Script [] (REAL ∷ REAL ∷ REAL ∷ []) (SAT ∷ [])
script = withReflectedNetworkAsScript model $ λ where
  (i₀ ∷ i₁ ∷ []) (o₀ ∷ [])
    → assert (((i₀ == 0·0f) ∧ (i₁ == 0·0f)) ⇒ (o₀ == 0·0f))
    ∷ assert (((i₀ == 0·0f) ∧ (i₁ == 1·0f)) ⇒ (o₀ == 0·0f))
    ∷ assert (((i₀ == 1·0f) ∧ (i₁ == 0·0f)) ⇒ (o₀ == 0·0f))
    ∷ assert (((i₀ == 1·0f) ∧ (i₁ == 1·0f)) ⇒ (o₀ == 1·0f))
    ∷ check-sat
    ∷ []

_ : z3 script ≡ sat ∷ []
_ = refl
