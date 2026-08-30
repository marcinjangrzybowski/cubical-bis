module Cubical.Analysis.Real.Calculus.Derivative.Power where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties

open import Cubical.Data.Nat using (ℕ; zero; suc)

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Algebra.Natural
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Calculus.Derivative.Base
open import Cubical.Analysis.Real.Calculus.Derivative.Basic
open import Cubical.Analysis.Real.Calculus.Derivative.Product
open import Cubical.Analysis.Real.Calculus.Derivative.Chain


private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)


-- Keeping the zero case separate makes the conventional derivative of x⁰
-- total, without choosing a value for x⁻¹.
naturalPowerDerivative : ℕ → ℝ → ℝ
naturalPowerDerivative zero _ = 0ℝ
naturalPowerDerivative (suc n) x =
  realNatural (suc n) · powℝ x n


private
  reassociatePowerCoefficient : ∀ x coefficient power →
    x · (coefficient · power)
      ≡
    coefficient · (x · power)
  reassociatePowerCoefficient x coefficient power =
    mulAssoc x coefficient power
    ∙ cong (_· power) (mulComm x coefficient)
    ∙ sym (mulAssoc coefficient x power)

  successorDerivativeValue : ∀ n x →
    1ℝ · powℝ x n + x · naturalPowerDerivative n x
      ≡
    naturalPowerDerivative (suc n) x
  successorDerivativeValue zero x =
    cong₂ _+_
      (mulIdL 1ℝ)
      (ℝRing.0RightAnnihilates x)
    ∙ addIdR 1ℝ
    ∙ sym (mulIdL 1ℝ)
  successorDerivativeValue (suc n) x =
    cong₂ _+_
      (mulIdL (x · powℝ x n))
      (reassociatePowerCoefficient
        x (realNatural (suc n)) (powℝ x n))
    ∙ addComm
        (x · powℝ x n)
        (realNatural (suc n) · (x · powℝ x n))
    ∙ cong
        (realNatural (suc n) · (x · powℝ x n) +_)
        (sym (mulIdL (x · powℝ x n)))
    ∙ sym
        (mulDistL
          (realNatural (suc n)) 1ℝ
          (x · powℝ x n))
    ∙ cong
        (_· (x · powℝ x n))
        (sym (realNatural-suc (suc n)))


naturalPowerHasDerivative : ∀ n →
  IsDerivative
    (λ x → powℝ x n)
    (naturalPowerDerivative n)
naturalPowerHasDerivative zero =
  constantHasDerivative 1ℝ
naturalPowerHasDerivative (suc n) =
  subst
    (IsDerivative (λ x → powℝ x (suc n)))
    (funExt (successorDerivativeValue n))
    (mulHasDerivative
      (idfun ℝ) (λ x → powℝ x n)
      (λ _ → 1ℝ) (naturalPowerDerivative n)
      identityHasDerivative (naturalPowerHasDerivative n))


zeroPowerHasDerivative :
  IsDerivative
    (λ x → powℝ x zero)
    (λ _ → 0ℝ)
zeroPowerHasDerivative = naturalPowerHasDerivative zero


successorPowerHasDerivative : ∀ n →
  IsDerivative
    (λ x → powℝ x (suc n))
    (λ x → realNatural (suc n) · powℝ x n)
successorPowerHasDerivative n = naturalPowerHasDerivative (suc n)


naturalPowerCompositionHasDerivativeAlong :
  ∀ {ℓ ℓ'} {A : Type ℓ}
    (source : PremetricStr ℓ' A)
    (coordinate function derivative : A → ℝ) →
  isContinuous source coordinate (ℝPremetricSpace .snd) →
  IsDerivativeAlong source coordinate function derivative →
  ∀ n →
  IsDerivativeAlong
    source coordinate
    (λ point → powℝ (function point) n)
    (λ point →
      naturalPowerDerivative n (function point) · derivative point)
naturalPowerCompositionHasDerivativeAlong
  source coordinate function derivative
  coordinate-continuous function-derivative n =
    chainHasDerivativeAlong
      source coordinate function derivative
      (λ x → powℝ x n) (naturalPowerDerivative n)
      coordinate-continuous function-derivative
      (naturalPowerHasDerivative n)


naturalPowerCompositionHasDerivative :
  ∀ function derivative →
  IsDerivative function derivative →
  ∀ n →
  IsDerivative
    (λ x → powℝ (function x) n)
    (λ x →
      naturalPowerDerivative n (function x) · derivative x)
naturalPowerCompositionHasDerivative
  function derivative function-derivative n =
    chainHasDerivative
      function derivative
      (λ x → powℝ x n) (naturalPowerDerivative n)
      function-derivative (naturalPowerHasDerivative n)
