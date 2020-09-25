--------------------------------------------------------------------------------
-- Amethyst: Neural Network Verification in Agda
--
-- This module exports some basic configuration settings for the representation
-- of networks
--------------------------------------------------------------------------------

module Amethyst.Network.Approximation where

open import Data.Nat.Base using (ℕ)
open import Data.Float.Base
open import Data.Unit
open import Amethyst.PiecewiseLinear.Base

module Exp where

  segments = 15
  min = -8.0
  max = 8.0
  lowerOutOfBounds = constant 0.0
  upperOutOfBounds = extrapolate

  approx : PiecewiseLinearFn
  approx = linearise (e^_) min max segments lowerOutOfBounds upperOutOfBounds

open Exp public using () renaming (approx to expApprox)


-- The sigmoid function is not defined in terms of the Exp in order
-- to avoid a loss in precision at extreme values when taking the
-- reciprocal.
module Sigmoid where

  segments = 15
  min = -8.0
  max = 8.0
  lowerOutOfBounds = constant 0.0
  upperOutOfBounds = constant 1.0

  approx : PiecewiseLinearFn
  approx = linearise (λ x → 1.0 ÷ (1.0 + e^ - x)) min max segments lowerOutOfBounds upperOutOfBounds

open Sigmoid public using () renaming (approx to sigmoidApprox)


module HyperbolicTangent where

  segments = 15
  min = -3.0
  max = 3.0
  lowerOutOfBounds = constant 0.0
  upperOutOfBounds = constant 1.0
  
  approx : PiecewiseLinearFn
  approx = linearise tanh -3.0 3.0 3 lowerOutOfBounds upperOutOfBounds

open HyperbolicTangent public using () renaming (approx to tanhApprox)
