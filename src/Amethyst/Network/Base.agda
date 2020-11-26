--------------------------------------------------------------------------------
-- Amethyst: Neural Network Verification in Agda
--
-- This module exports the basic types for representing neural networks.
--
-- Exports:
--
--   - Activation (linear; relu; sigmoid; softmax; tanh)
--   - Layer      (activation; weights; biases)
--   - Network    ([]; _∷_)
--
--------------------------------------------------------------------------------

module Amethyst.Network.Base where

import Data.Vec.Extra as Vec

open import Data.Fin.Base as Fin using (Fin)
open import Data.Float as Float using (Float)
open import Data.Nat.Base as Nat using (ℕ; suc; zero)
open import Data.Vec.Base as Vec using (Vec; []; _∷_)
open import Function using (id)

private
  variable
    A : Set
    n : ℕ
    hidden  : ℕ
    layers  : ℕ

data Activation : Set where
  linear  : Activation
  relu    : Activation
  sigmoid : Activation
  softmax : Activation
  tanh    : Activation

record Layer (A : Set) (inputs outputs : ℕ) : Set where
  field
    activation : Activation
    weights    : Vec (Vec A outputs) inputs
    biases     : Vec A outputs

LayerSpec : ℕ → Set
LayerSpec = Vec ℕ

∣_₀∣ : LayerSpec n → ℕ
∣ xs ₀∣ = Vec.headOr xs 0

∣_ₙ∣ : LayerSpec n → ℕ
∣ xs ₙ∣ = Vec.lastOr xs 0

infixr 5 _∷_

data Network (A : Set) : ∀ {#layers : ℕ} → Vec ℕ #layers → Set where
  []  : ∀ {n} → Network A (n ∷ [])
  _∷_ : ∀ {n |lᵢ| |lᵢ₊₁|} {xs : LayerSpec n} →
        Layer A |lᵢ| |lᵢ₊₁| → Network A (|lᵢ₊₁| ∷ xs) → Network A (|lᵢ| ∷ |lᵢ₊₁| ∷ xs)
