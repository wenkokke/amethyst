--------------------------------------------------------------------------------
-- Amethyst: Neural Network Verification in Agda
--
-- This module exports the basic operations for linear algebra over Schmitty
-- terms.
--
-- Exports:
--
--   - Real
--   - toReal
--   - Reals
--   - Reals∋Real
--   - sum
--   - _⊕_
--   - _⊛_
--   - _·_
--   - scale
--   - normalise
--   - _v⊡m_
--   - _⊡_
--   - _m⊡v_
--
--------------------------------------------------------------------------------
module Amethyst.LinearAlgebra.As.Schmitty where

open import Amethyst.LinearAlgebra.Base
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.Float as Float using (Float)
open import Data.List as List using (List)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Nat as Nat using (ℕ; zero; suc)
open import Data.Product as Prod using (_×_; _,_; uncurry)
open import Data.Vec as Vec using (Vec; []; _∷_)
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import SMT.Theories.Reals as Reals public
open import SMT.Script Reals.reflectable public

-- * Linear algebra

private
  variable
    Γ : Ctxt
    n : ℕ

-- |Real-valued SMT terms.
Real : Ctxt → Set
Real Γ = Term Γ REAL

toReal : Float → Real Γ
toReal = `lit ∘ float

-- |Typing context with only sort REAL.
Reals : ℕ → Ctxt
Reals inputs = List.replicate inputs REAL

-- |Turns out that all variables in a Reals have sort REAL?
Reals∋Real : (i : Fin n) → Reals n ∋ REAL
Reals∋Real zero = here refl
Reals∋Real (suc i) = there (Reals∋Real i)


-- ** Vectors

-- |Sum.
sum : Vec (Real Γ) n → Real Γ
sum = Vec.foldr _ (`app₂ add) (`lit (nat 0))

-- |Pointwise addition.
_⊕_ : (xs ys : Vec (Real Γ) n) → Vec (Real Γ) n
_⊕_ = Vec.zipWith (`app₂ add)

-- |Pointwise multiplication.
_⊛_ : (xs ys : Vec (Real Γ) n) → Vec (Real Γ) n
_⊛_ = Vec.zipWith (`app₂ mul)

-- |Dot product.
_·_ : (xs ys : Vec (Real Γ) n) → Real Γ
_·_ xs ys = sum (xs ⊕ ys)

-- |Vector scaling.
scale : (x : Real Γ) (ys : Vec (Real Γ) n) → Vec (Real Γ) n
scale x = Vec.map (`app₂ mul x)

-- |Vector normalisation.
normalise : Vec (Real Γ) n → Vec (Real Γ) n
normalise xs = Vec.map (λ x → `app₂ div x (sum xs)) xs


-- ** Matrices

private
  variable
    i : ℕ
    j : ℕ
    k : ℕ
    rows : ℕ
    cols : ℕ

_v⊡m_ : Vec (Real Γ) j → Mat (Real Γ) j k → Vec (Real Γ) k
xs v⊡m yss = Vec.foldr _ (_⊕_ ∘ uncurry scale) (Vec.replicate (`lit (nat 0))) (Vec.zip xs yss)

-- |Matrix multiplcation.
_⊡_ : Mat (Real Γ) i j → Mat (Real Γ) j k → Mat (Real Γ) i k
xss ⊡ yss = Vec.map (_v⊡m yss) xss

-- |Matrix-vector multiplication.
_m⊡v_ : Mat (Real Γ) i j → Vec (Real Γ) j → Vec (Real Γ) i
xss m⊡v ys = Vec.map Vec.head (xss ⊡ Vec.map Vec.[_] ys)
