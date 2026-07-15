module Cubical.HITs.CauchyReals.Exponentiation.ExpLog.Derivative where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset
open import Cubical.Functions.FunExtEquiv

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base using (⊤Pred)
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Calculus.Derivative.Base hiding (invℚ₊)
open import Cubical.HITs.CauchyReals.Exponentiation.RealPower.Calculus
open import Cubical.HITs.CauchyReals.Exponentiation.Normalized.Exponential

realExpDerivative :
  DerivativeOfℙ ⊤Pred , (λ x _ → fst (realExp x)) is
    (λ x _ → fst (realExp x))
realExpDerivative =
  subst
    (DerivativeOfℙ ⊤Pred , (λ x _ → fst (realExp x)) is_)
    (funExt₂ λ x _ →
      cong (fst (realExp x) ·ᵣ_) ln-eBase ∙ ·IdR _)
    (realPowerDerivative eBase)
