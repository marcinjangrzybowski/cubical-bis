module Cubical.HITs.CauchyReals.Exponentiation.RealPowerCalculus where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset

open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Derivative hiding (invℚ₊)
open import Cubical.HITs.CauchyReals.ExponentiationMore
open import Cubical.HITs.CauchyReals.Exponentiation.RealPowerCalculusProof
  using (realPowerDerivativeProof; ln-realPowerProof)

opaque
  -- Previous name: ^-der, for the quotient-slope derivative.
  realPowerDerivative : ∀ x →
    DerivativeOfℙ ⊤Pred , (λ y _ → fst (x ^ᵣ y)) is
      (λ y _ → fst (x ^ᵣ y) ·ᵣ ln x)
  realPowerDerivative = realPowerDerivativeProof

  -- Previous names: ln[a^b₊]≡b₊·ln[a], ln[a^b]≡b·ln[a].
  ln-realPower : ∀ a b → ln (a ^ᵣ b) ≡ b ·ᵣ ln a
  ln-realPower = ln-realPowerProof
