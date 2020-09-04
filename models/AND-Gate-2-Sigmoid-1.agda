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

script : Script [] (Reals 2 ++ Reals 1) (SAT ∷ [])
script = withReflectedNetworkAsScript model $ λ where
  -- give names to input and output nodes
  iv@(i₀ ∷ i₁ ∷ []) ov@(o₀ ∷ [])
  -- give remainder of the smt-lib script
    → assert (((i₀ == 0·0f) ∧ (i₁ == 0·0f)) ⇒ (o₀ == 0·0f))
    ∷ assert (((i₀ == 0·0f) ∧ (i₁ == 1·0f)) ⇒ (o₀ == 0·0f))
    ∷ assert (((i₀ == 1·0f) ∧ (i₁ == 0·0f)) ⇒ (o₀ == 0·0f))
    ∷ assert (((i₀ == 1·0f) ∧ (i₁ == 1·0f)) ⇒ (o₀ == 1·0f))
    ∷ check-sat
    ∷ []

_ : z3 script ≡ sat ∷ []
_ = refl

_ : evalNetwork model (0.0 ∷ 0.0 ∷ []) ≡ (0.0 ∷ [])
_ = refl
_ : evalNetwork model (0.0 ∷ 1.0 ∷ []) ≡ (0.0 ∷ [])
_ = refl
_ : evalNetwork model (1.0 ∷ 0.0 ∷ []) ≡ (0.0 ∷ [])
_ = refl
_ : evalNetwork model (1.0 ∷ 1.0 ∷ []) ≡ (1.0 ∷ [])
_ = refl
