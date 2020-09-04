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

open import Amethyst.Network.Base using (Network; []; _∷_; Layer; Activation)
open import Amethyst.PiecewiseLinear.Base
open import Amethyst.PiecewiseLinear.As.Schmitty
open import Amethyst.LinearAlgebra.As.Schmitty
open import Data.Bool as Bool using (Bool; false; true)
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.Float as Float using (Float)
open import Data.List as List using (List; []; _∷_; _++_; _ʳ++_)
import Data.List.Properties as List
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
  relu x = app₃ ite (app₂ leq x (lit (nat 0))) (lit (nat 0)) x

  lexp : Real Γ → Real Γ
  lexp = reflectExtrap (linearise Float.e^_ -4.0 4.0 15)

  lsigmoid : Real Γ → Real Γ
  lsigmoid x = app₂ div (toReal 1.0) (app₂ add (toReal 1.0) (lexp (app₁ neg x)))

  lsoftmax : Vec (Real Γ) n → Vec (Real Γ) n
  lsoftmax xs = normalise (Vec.map lexp xs)

  ltanh : Real Γ → Real Γ
  ltanh = reflectExtrap (linearise Float.tanh -3.0 3.0 3)

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
reflectNetwork : Network Float inputs outputs layers → Vec (Real Γ) inputs → Vec (Real Γ) outputs
reflectNetwork []      = id
reflectNetwork (l ∷ n) = reflectNetwork n ∘ reflectLayer l

private
  -- |The reverse-append of two reversed lists is equivalent to the append of the lists.
  --
  --  NOTE: The variable contexts for a Script are in reversed order, so we pass
  --        the reversed input/output contexts to `declare-consts` to ensure
  --        that we end up with *doubly* reversed contexts in the Script.
  --        We use this lemma to show that the doubly reversed contexts are
  --        equivalent to the original input/output context.
  --
  --  NOTE: Perhaps this lemma should be submitted to Data.List.Properties?
  --
  ʳ++-reverse : ∀ {a} {A : Set a} (xs ys : List A) → List.reverse xs ʳ++ List.reverse ys  ʳ++ [] ≡ xs ++ ys
  ʳ++-reverse xs ys =
    begin
      List.reverse xs ʳ++ List.reverse ys ʳ++ []
    ≡⟨ List.ʳ++-defn (List.reverse xs) ⟩
      List.reverse (List.reverse xs) ++ List.reverse ys  ʳ++ []
    ≡⟨ List.reverse-involutive xs |> Eq.cong (_++ List.reverse ys ʳ++ []) ⟩
      xs ++ List.reverse ys ʳ++ []
    ≡⟨ List.ʳ++-defn (List.reverse ys) |> Eq.cong (xs ++_) ⟩
      xs ++ List.reverse (List.reverse ys) ++ []
    ≡⟨ List.reverse-involutive ys |> Eq.cong ((xs ++_) ∘ (_++ [])) ⟩
      xs ++ ys ++ []
    ≡⟨ List.++-identityʳ ys |> Eq.cong (xs ++_) ⟩
      xs ++ ys
    ∎


-- |Convert a networks to an SMT script, and allow the caller to append further commands.
withReflectedNetworkAsScript
  : ∀ {Γ Ξ}
  → Network Float inputs outputs layers
  → ( (iv : Vec (Real (Reals inputs ++ Reals outputs)) inputs)
    → (ov : Vec (Real (Reals inputs ++ Reals outputs)) outputs)
    → (Script (Reals inputs ++ Reals outputs) Γ Ξ))
    → Script [] Γ Ξ
withReflectedNetworkAsScript {inputs} {outputs} n k
  = ( Eq.subst (λ Γ → Script [] Γ []) (ʳ++-reverse (Reals inputs) (Reals outputs))
    $ declare-consts (List.reverse (Reals outputs))
    $ declare-consts (List.reverse (Reals inputs))
    $ assert
      (Vec.foldr _
        (app₂ and)
        (lit (bool true))
        (Vec.zipWith
          (app₂ eq)
          (Eq.subst (λ Γ → Vec (Real Γ) outputs) (Eq.sym (ʳ++-reverse (Reals inputs) (Reals outputs))) ov)
          (reflectNetwork n
            (Eq.subst (λ Γ → Vec (Real Γ) inputs) (Eq.sym (ʳ++-reverse (Reals inputs) (Reals outputs))) iv))))
    ∷ []
    ) ◆ k iv ov
  where
  iv = Vec.map (var ∘ injectVar (Reals inputs) ∘ Reals∋Real) (Vec.allFin inputs)
  ov = Vec.map (var ∘ raiseVar  (Reals inputs) ∘ Reals∋Real) (Vec.allFin outputs)
