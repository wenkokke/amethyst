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
  NetworkCtxt : (inputs outputs : ℕ) → Ctxt
  NetworkCtxt inputs outputs = RealCtxt inputs ++ RealCtxt outputs


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

-- |Convert networks to SMT scripts.
toScript : Network Float inputs outputs layers → Script [] (NetworkCtxt inputs outputs) []
toScript {inputs} {outputs} n
  = Eq.subst (λ Γ → Script [] Γ []) (ʳ++-reverse (RealCtxt inputs) (RealCtxt outputs))
  $ declare-consts (List.reverse (RealCtxt outputs))
  $ declare-consts (List.reverse (RealCtxt inputs))
  $ assert
      (Vec.foldr _
        (app₂ and)
        (lit (bool true))
        (Vec.zipWith
          (app₂ eq)
          (Eq.subst
            (λ Γ → Vec (Real Γ) outputs)
            (Eq.sym (ʳ++-reverse (RealCtxt inputs) (RealCtxt outputs)))
            outputVec)
          (reflectNetwork n
            (Eq.subst
              (λ Γ → Vec (Real Γ) inputs)
              (Eq.sym (ʳ++-reverse (RealCtxt inputs) (RealCtxt outputs)))
              inputVec))))
  ∷ []
  where
    inputVec : Vec (Real (NetworkCtxt inputs outputs)) inputs
    inputVec = Vec.map (var ∘ injectVar (RealCtxt inputs) ∘ RealCtxt∋REAL) (Vec.allFin inputs)
    outputVec : Vec (Real (NetworkCtxt inputs outputs)) outputs
    outputVec = Vec.map (var ∘ raiseVar (RealCtxt inputs) ∘ RealCtxt∋REAL) (Vec.allFin outputs)
