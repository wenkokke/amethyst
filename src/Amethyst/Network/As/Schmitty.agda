--------------------------------------------------------------------------------
-- Amethyst: Neural Network Verification in Agda
--
-- This module contains functions to reflect networks as Schmitty terms. It also
-- provides the `withReflectedNetwork` function, which reflects a network as a
-- Schmitty term, and wraps that term in a script which declares the appropriate
-- constants for the inputs and outputs, and allows the caller to append further
-- portions of script.
--
-- Exports:
--
--   - reflectActivation
--   - reflectLayer
--   - reflectNetwork
--   - withReflectedNetworkAsScript
--
--------------------------------------------------------------------------------
module Amethyst.Network.As.Schmitty where

open import SMT.Theories.Reals.Base using (true)

open import Amethyst.Network.Base
  using (Network; []; _∷_; Layer; LayerSpec; Activation; ∣_₀∣; ∣_ₙ∣)
open import Amethyst.Network.Approximation
open import Amethyst.PiecewiseLinear.Base
open import Amethyst.PiecewiseLinear.As.Schmitty
open import Amethyst.LinearAlgebra.As.Schmitty
import Amethyst.Data.Vec as Vec

open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.Float as Float using (Float)
open import Data.List as List using (List; []; _∷_; _++_; _ʳ++_)
open import Data.List.Relation.Unary.All using ([])
import Data.List.Properties as List
import Data.List.Properties.Extra as List
open import Data.Nat as Nat using (ℕ; zero; suc)
open import Data.Product as Prod using (_×_; _,_; uncurry)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Function using (_$_; _∘_; _|>_; id)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open Eq.≡-Reasoning

-- * Activation functions

private
  variable
    Γ : Ctxt
    n : ℕ

private
  relu : Real Γ → Real Γ
  relu x = `app₃ ite (`app₂ leq x (`lit (nat 0))) (`lit (nat 0)) x

  lexp : Real Γ → Real Γ
  lexp = reflect expApprox

  lsigmoid : Real Γ → Real Γ
  lsigmoid = reflect sigmoidApprox

  lsoftmax : Vec (Real Γ) n → Vec (Real Γ) n
  lsoftmax xs = normalise (Vec.map lexp xs)

  ltanh : Real Γ → Real Γ
  ltanh = reflect tanhApprox


-- |Convert activation functions to SMT terms.
--
--  Takes an activation function description and an environment of SMT terms
--  describing the activation function inputs, and returns an environment of SMT
--  terms with the activation function applied.
reflectActivation : Activation → Vec (Real Γ) n → Vec (Real Γ) n
reflectActivation Activation.linear  = id
reflectActivation Activation.relu    = Vec.map relu
reflectActivation Activation.sigmoid = Vec.map lsigmoid
reflectActivation Activation.softmax = lsoftmax
reflectActivation Activation.tanh    = Vec.map ltanh


-- * Neural networks

private
  variable
    inputs  : ℕ
    hidden  : ℕ
    outputs : ℕ
    layers  : ℕ

-- |Convert layers to SMT terms.
--
--  Takes a layer description and an environment of SMT terms describing the
--  layer inputs, and returns an environment of SMT terms describing the layer
--  outputs.
reflectLayer : Layer Float inputs outputs → Vec (Real Γ) inputs → Vec (Real Γ) outputs
reflectLayer l xs = reflectActivation activation (biases′ ⊕ (xs v⊡m weights′))
  where
    open Layer l using (activation; weights; biases)
    biases′  = Vec.map toReal biases
    weights′ = Vec.map (Vec.map toReal) weights

-- |Convert networks to SMT terms.
--
--  Takes a network description and an environment of SMT terms describing the
--  network inputs, and returns an environment of SMT terms describing the network
--  outputs.
reflectNetwork : ∀ {n} {xs : Vec ℕ n} → Network Float xs → Vec (Real Γ) ∣ xs ₀∣ → Vec (Real Γ) ∣ xs ₙ∣
reflectNetwork []      = id
reflectNetwork (l ∷ n) = reflectNetwork n ∘ reflectLayer l

-- |Convert a networks to an SMT script, and allow the caller to append further commands.
withReflectedNetworkAsScript
  : ∀ {Γ Ξ} {ls : LayerSpec layers}
  → Network Float ls
  → ( (iv : Vec (Real (Reals ∣ ls ₀∣ ++ Reals ∣ ls ₙ∣)) ∣ ls ₀∣)
    → (ov : Vec (Real (Reals ∣ ls ₀∣ ++ Reals ∣ ls ₙ∣)) ∣ ls ₙ∣)
    → (Script (Reals ∣ ls ₀∣ ++ Reals ∣ ls ₙ∣) Γ Ξ))
  → Script [] Γ Ξ
withReflectedNetworkAsScript {ls = ls} n constraints
  = ( Eq.subst (λ Γ → Script [] Γ []) (List.ʳ++-reverse (Reals ∣ ls ₀∣) (Reals ∣ ls ₙ∣))
    $ `declare-consts (List.reverse (Reals ∣ ls ₙ∣))
    $ `declare-consts (List.reverse (Reals ∣ ls ₀∣))
    $ `assert (Vec.foldr _
        (`app₂ and)
        (`app₀ true)
        (Vec.zipWith
          (`app₂ eq)
          (Eq.subst (λ Γ → Vec (Real Γ) ∣ ls ₙ∣) (Eq.sym (List.ʳ++-reverse (Reals ∣ ls ₀∣) (Reals ∣ ls ₙ∣))) ov)
          (reflectNetwork n
            (Eq.subst (λ Γ → Vec (Real Γ) ∣ ls ₀∣) (Eq.sym (List.ʳ++-reverse (Reals ∣ ls ₀∣) (Reals ∣ ls ₙ∣))) iv))))
    ∷ []
    ) ◆ constraints iv ov
  where
  iv = Vec.map (`var ∘ injectVar (Reals ∣ ls ₀∣) ∘ Reals∋Real) (Vec.allFin ∣ ls ₀∣)
  ov = Vec.map (`var ∘ raiseVar  (Reals ∣ ls ₀∣) ∘ Reals∋Real) (Vec.allFin ∣ ls ₙ∣)
