
module Amethyst.Data.Vec where

open import Data.Fin using (fromℕ)
open import Data.Vec.Base
open import Data.Nat using (ℕ; zero; suc)
open import Level using (Level)

private
  variable
    a : Level
    A : Set a
    n : ℕ

first′ : Vec A n → A → A
first′ {n = zero}  _            v = v
first′ {n = suc n} (x ∷ xs) v = x

last′ : Vec A n → A → A
last′ {n = zero}  xs v = v
last′ {n = suc n} xs v = lookup xs (fromℕ n)
