--------------------------------------------------------------------------------
-- Amethyst: Neural Network Verification in Agda
--
-- This module exports the basic operations for linear algebra. The definitions
-- in this module should work regardless of carrier, i.e., whether the carrier
-- is Float, Schmitty terms, or whatever.
--
-- Exports:
--
--   - Mat
--
--------------------------------------------------------------------------------
module Amethyst.LinearAlgebra.Base where

open import Data.Nat as Nat using (ℕ)
open import Data.Vec as Vec using (Vec)

Mat : (A : Set) (rows cols : ℕ) → Set
Mat A rows cols = Vec (Vec A cols) rows
