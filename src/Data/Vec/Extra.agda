module Data.Vec.Extra where

open import Data.Fin using (fromℕ)
open import Data.Vec.Base
open import Data.Nat using (ℕ; zero; suc)
open import Level using (Level)

private
  variable
    a : Level
    A : Set a
    n : ℕ

headOr : Vec A n → A → A
headOr {n = zero}  _        v = v
headOr {n = suc n} (x ∷ xs) v = x

lastOr : Vec A n → A → A
lastOr {n = zero}  xs v = v
lastOr {n = suc n} xs v = lookup xs (fromℕ n)
