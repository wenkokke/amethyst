{-# OPTIONS --allow-exec #-}

module AND-Gate-2-Sigmoid-1 where

open import Amethyst.Network
open import Data.Float
open import Data.List as List using (List; []; _∷_)
open import Data.Product as Prod using (_×_; proj₁; proj₂)
open import Data.String as String using (String)
open import Data.Vec as Vec using (Vec; []; _∷_; [_])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import SMT.Theories.Reals as Reals
open import SMT.Script Reals.theory
open import SMT.Backend.Z3 Reals.theory

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

modelAsScript : Script [] (REAL ∷ REAL ∷ REAL ∷ []) (SAT ∷ [])
modelAsScript
  = reflectNetworkAsScript model
  ◆ assert (((i₀ == 0·0f) ∧ (i₁ == 0·0f)) ⇒ (o₀ == 0·0f))
  ∷ assert (((i₀ == 0·0f) ∧ (i₁ == 1·0f)) ⇒ (o₀ == 0·0f))
  ∷ assert (((i₀ == 1·0f) ∧ (i₁ == 0·0f)) ⇒ (o₀ == 0·0f))
  ∷ assert (((i₀ == 1·0f) ∧ (i₁ == 1·0f)) ⇒ (o₀ == 1·0f))
  ∷ check-sat
  ∷ []
  where
    -- Variables
    i₀ = # 0
    i₁ = # 1
    o₀ = # 2
    -- Logical connectives
    _⇒_ = app₂ implies
    _∧_ = app₂ and
    _==_ = app₂ eq
    -- Floating-point numbers
    0·0f = lit (float 0.0)
    1·0f = lit (float 1.0)

_ : z3 modelAsScript ≡ sat ∷ []
_ = refl
