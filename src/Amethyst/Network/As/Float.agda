--------------------------------------------------------------------------------
-- Amethyst: Neural Network Verification in Agda
--
-- This module contains functions to evaluate neural networks as functions on
-- vectors of floating-point numbers.
--
-- Exports:
--
--  - evalActivation
--  - evalLayer
--  - evalNetwork
--
--------------------------------------------------------------------------------
module Amethyst.Network.As.Float where

open import Amethyst.Network.Base
  using (Network; []; _∷_; Layer; Activation; LayerSpec; ∣_₀∣; ∣_ₙ∣)
open import Amethyst.Network.Approximation
open import Amethyst.LinearAlgebra.As.Float
open import Amethyst.PiecewiseLinear.As.Float
import Amethyst.Data.Vec as Vec

open import Data.Bool as Bool using (if_then_else_)
open import Data.Fin as Fin using ()
open import Data.Float as Float using (Float; _≤ᵇ_; _+_; _-_; _*_; _÷_; -_; e^_; tanh)
open import Data.Nat as Nat using (ℕ; zero; suc)
open import Data.Product using (uncurry)
open import Data.Vec as Vec using (Vec)
open import Function using (_∘_; const; id)

-- * Activation functions

private
  variable
    n : ℕ

  relu : Float → Float
  relu x = if x ≤ᵇ 0.0 then 0.0 else x

  sigmoid : Float → Float
  sigmoid x = eval sigmoidApprox x

  softmax : Vec Float n → Vec Float n
  softmax xs = normalise (Vec.map (eval expApprox) xs)

-- * Neural networks

private
  variable
    inputs  : ℕ
    outputs : ℕ
    layers  : ℕ
  
-- |Eval an activation function as a function on vectors of floats.
evalActivation : Activation → Vec Float n → Vec Float n
evalActivation Activation.linear  = id
evalActivation Activation.relu    = Vec.map relu
evalActivation Activation.sigmoid = Vec.map sigmoid
evalActivation Activation.softmax = softmax
evalActivation Activation.tanh    = Vec.map tanh

-- |Eval a network layer as a function on vectors of floats.
evalLayer : Layer Float inputs outputs → Vec Float inputs → Vec Float outputs
evalLayer l xs = evalActivation activation (biases ⊕ (xs v⊡m weights))
  where
    open Layer l using (activation; biases; weights)

-- |Eval a network as a function on vectors of floats.
evalNetwork : ∀ {ls : LayerSpec layers} → Network Float ls →
              Vec Float ∣ ls ₀∣ → Vec Float ∣ ls ₙ∣
evalNetwork []      = id
evalNetwork (l ∷ n) = evalNetwork n ∘ evalLayer l
