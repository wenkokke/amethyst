module Amethyst.Network where

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
    weights    : Vec (Vec A outputs) inputs
    biases     : Vec A outputs
    activation : Activation

infixr 5 _∷_

data Network (A : Set) (inputs : ℕ) : (outputs layers : ℕ) → Set where
  []  : Network A inputs inputs 0
  _∷_ : Layer A inputs hidden → Network A hidden outputs layers → Network A inputs outputs (suc layers)
