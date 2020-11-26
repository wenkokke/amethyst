module Data.List.Properties.Extra where

open import Data.List as List using (List; []; _∷_; _++_; _ʳ++_)
import Data.List.Properties as List
open import Function using (_∘_; _|>_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open Eq.≡-Reasoning


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
