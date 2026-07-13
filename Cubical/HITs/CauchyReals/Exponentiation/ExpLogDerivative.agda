module Cubical.HITs.CauchyReals.Exponentiation.ExpLogDerivative where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset
open import Cubical.Functions.FunExtEquiv

open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Order using (⊤Pred)
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Derivative hiding (invℚ₊)
open import Cubical.HITs.CauchyReals.Exponentiation.RealPowerCalculus
open import Cubical.HITs.CauchyReals.Exponentiation.NormalizedExponential

realExpDerivative :
  DerivativeOfℙ ⊤Pred , (λ x _ → fst (realExp x)) is
    (λ x _ → fst (realExp x))
realExpDerivative =
  subst
    (DerivativeOfℙ ⊤Pred , (λ x _ → fst (realExp x)) is_)
    (funExt₂ λ x _ →
      cong (fst (realExp x) ·ᵣ_) ln-eBase ∙ ·IdR _)
    (realPowerDerivative eBase)
