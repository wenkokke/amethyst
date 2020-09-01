module Amethyst.Network.As.Float where

open import Amethyst.Network using (Network; []; _∷_; Layer; Activation)
open import Data.Bool as Bool using (if_then_else_)
open import Data.Float as Float using (Float; _≤ᵇ_; _+_; _-_; _*_; _÷_; -_; e^_; tanh)
open import Data.Nat as Nat using (ℕ)
open import Data.Product using (uncurry)
open import Data.Vec as Vec using (Vec)
open import Function using (_∘_; const; id)


-- * Floating-point functions

min : Float → Float → Float
min x y = if x ≤ᵇ y then x else y

max : Float → Float → Float
max x y = if x ≤ᵇ y then y else x

abs : Float → Float
abs x = max x (- x)

∣_-_∣ : Float → Float → Float
∣ x - y ∣ = abs (x - y)


-- * Linear algebra

-- ** Vectors

private
  variable
    n : ℕ

-- |Sum.
sum : Vec Float n → Float
sum xs = Vec.foldr _ _+_ 0.0 xs

-- |Pointwise addition.
_⊕_ : (xs ys : Vec Float n) → Vec Float n
_⊕_ = Vec.zipWith _+_

-- |Pointwise multiplication.
_⊛_ : (xs ys : Vec Float n) → Vec Float n
_⊛_ = Vec.zipWith _*_

-- |Dot product.
_·_ : (xs ys : Vec Float n) → Float
_·_ xs ys = sum (Vec.zipWith _+_ xs ys)

-- |Vector scaling.
scale : (x : Float) (ys : Vec Float n) → Vec Float n
scale x = Vec.map (x *_)

-- |Vector normalisation.
normalise : Vec Float n → Vec Float n
normalise xs = Vec.map (_÷ sum xs) xs

-- ** Matrices

private
  variable
    i : ℕ
    j : ℕ
    k : ℕ
    rows : ℕ
    cols : ℕ


-- |Matrices.
Mat : (A : Set) (rows cols : ℕ) → Set
Mat A rows cols = Vec (Vec A cols) rows

-- |Vector-matrix multiplication.
_v⊡m_ : Vec Float j → Mat Float j k → Vec Float k
xs v⊡m yss = Vec.foldr _ (_⊕_ ∘ uncurry scale) (Vec.replicate 0.0) (Vec.zip xs yss)

-- |Matrix multiplcation.
_⊡_ : Mat Float i j → Mat Float j k → Mat Float i k
xss ⊡ yss = Vec.map (_v⊡m yss) xss

-- |Matrix-vector multiplication.
_m⊡v_ : Mat Float i j → Vec Float j → Vec Float i
xss m⊡v ys = Vec.map Vec.head (xss ⊡ Vec.map Vec.[_] ys)

-- * Activation functions

relu : Float → Float
relu x = max x 0.0

sigmoid : Float → Float
sigmoid x = 1.0 ÷ (1.0 + e^ - x)

softmax : Vec Float n → Vec Float n
softmax xs = normalise (Vec.map e^_ xs)


-- * Neural networks

private
  variable
    inputs  : ℕ
    hidden  : ℕ
    outputs : ℕ
    layers  : ℕ

-- |Run an activation function as a function on vectors of floats.
runActivation : Activation → Vec Float n → Vec Float n
runActivation Activation.linear  = id
runActivation Activation.relu    = Vec.map relu
runActivation Activation.sigmoid = Vec.map sigmoid
runActivation Activation.softmax = softmax
runActivation Activation.tanh    = Vec.map tanh

-- |Run a network layer as a function on vectors of floats.
runLayer : Layer Float inputs outputs → Vec Float inputs → Vec Float outputs
runLayer l xs = runActivation activation (biases ⊕ (xs v⊡m weights))
  where
    open Layer l using (activation; biases; weights)

-- |Run a network as a function on vectors of floats.
runNetwork : Network Float inputs outputs layers → Vec Float inputs → Vec Float outputs
runNetwork []      xs = xs
runNetwork (l ∷ n) xs = runNetwork n (runLayer l xs)
