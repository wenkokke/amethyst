module Amethyst.LinearAlgebra.As.Float where

open import Amethyst.Network using (Network; []; _∷_; Layer; Activation)
open import Amethyst.LinearAlgebra.Base
open import Data.Bool as Bool using (if_then_else_)
open import Data.Float as Float using (Float; _≤ᵇ_; _+_; _-_; _*_; _÷_; -_; e^_; tanh)
open import Data.Nat as Nat using (ℕ)
open import Data.Product using (uncurry)
open import Data.Vec as Vec using (Vec)
open import Function using (_∘_; const; id)

-- * Linear algebra

-- ** Vectors

private
  variable
    n : ℕ

-- |Sum.
sum : Vec Float n → Float
sum = Vec.foldr _ _+_ 0.0

-- |Pointwise addition.
_⊕_ : (xs ys : Vec Float n) → Vec Float n
_⊕_ = Vec.zipWith _+_

-- |Pointwise multiplication.
_⊛_ : (xs ys : Vec Float n) → Vec Float n
_⊛_ = Vec.zipWith _*_

-- |Dot product.
_·_ : (xs ys : Vec Float n) → Float
_·_ xs ys = sum (xs ⊕ ys)

-- |Vector scaling.
scale : (x : Float) (ys : Vec Float n) → Vec Float n
scale x = Vec.map (x *_)

-- |Vector normalisation.
normalise : Vec Float n → Vec Float n
normalise xs = Vec.map (_÷ sum xs) xs

private
  variable
    i : ℕ
    j : ℕ
    k : ℕ
    rows : ℕ
    cols : ℕ

-- |Vector-matrix multiplication.
_v⊡m_ : Vec Float j → Mat Float j k → Vec Float k
xs v⊡m yss = Vec.foldr _ (_⊕_ ∘ uncurry scale) (Vec.replicate 0.0) (Vec.zip xs yss)

-- |Matrix multiplcation.
_⊡_ : Mat Float i j → Mat Float j k → Mat Float i k
xss ⊡ yss = Vec.map (_v⊡m yss) xss

-- |Matrix-vector multiplication.
_m⊡v_ : Mat Float i j → Vec Float j → Vec Float i
xss m⊡v ys = Vec.map Vec.head (xss ⊡ Vec.map Vec.[_] ys)
