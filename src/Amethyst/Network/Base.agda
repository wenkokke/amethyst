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

open import Data.Fin as Fin using (Fin)
open import Data.Float as Float using (Float)
open import Data.Nat as Nat using (ℕ; suc; zero)
open import Data.Vec as Vec using (Vec)
open import Function using (id)

private
  variable
    A : Set
    n : ℕ
    inputs  : ℕ
    hidden  : ℕ
    outputs : ℕ
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

infixr 5 _∷_

data Network (A : Set) (inputs : ℕ) : (outputs layers : ℕ) → Set where
  []  : Network A inputs inputs 0
  _∷_ : Layer A inputs hidden → Network A hidden outputs layers → Network A inputs outputs (suc layers)
