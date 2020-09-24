--------------------------------------------------------------------------------
-- Amethyst Models: Examples of Neural Network Verification in Agda
--
-- This module contains an example use of Amethyst, to verify the correctness of
-- the identity function network.
--------------------------------------------------------------------------------

{-# OPTIONS --allow-exec #-}

module Identity-1-Linear-1 where

open import Amethyst.Prelude
open import Data.Float using (Float)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

layer : Layer Float 1 1
layer = record
  { weights    = [ 1.0 ] ∷ []
  ; biases     = [ 0.0 ]
  ; activation = linear
  }

model : Network Float 1 1 1
model = layer ∷ []

_ : evalNetwork model (0.0 ∷ []) ≡ (0.0 ∷ [])
_ = refl
_ : evalNetwork model (1.0 ∷ []) ≡ (1.0 ∷ [])
_ = refl


-- Test some valid constraints

constraints : NetworkConstraints 1 1
constraints (i ∷ []) (o ∷ []) =
  (i == 0·0f ⇒ o == 0·0f) ∷
  (i == 1·0f ⇒ o == 1·0f) ∷
  []

_ : z3 (query model constraints) ≡ unsat ∷ []
_ = refl


-- Test some invalid constraints

invalidConstraints : NetworkConstraints 1 1
invalidConstraints (i ∷ []) (o ∷ []) =
  (i == 0·0f ⇒ o == 1·0f) ∷
  (i == 1·0f ⇒ o == 1·0f) ∷
  []

_ : z3 (query model invalidConstraints) ≡ sat ∷ []
_ = refl
