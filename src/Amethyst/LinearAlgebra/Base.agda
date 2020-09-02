module Amethyst.LinearAlgebra.Base where

open import Data.Nat as Nat using (ℕ)
open import Data.Vec as Vec using (Vec)

Mat : (A : Set) (rows cols : ℕ) → Set
Mat A rows cols = Vec (Vec A cols) rows
