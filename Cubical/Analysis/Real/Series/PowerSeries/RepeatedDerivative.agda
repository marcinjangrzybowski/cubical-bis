module Cubical.Analysis.Real.Series.PowerSeries.RepeatedDerivative where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat using (ℕ; zero; suc)
import Cubical.Data.Nat as Nat
import Cubical.Data.Nat.Properties as NatProperties

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.Natural
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Operations
open import Cubical.Analysis.Real.Series.PowerSeries.Derivative


repeatedFormalDerivative : ℕ → RealSequence → RealSequence
repeatedFormalDerivative zero coefficients = coefficients
repeatedFormalDerivative (suc order) coefficients =
  formalDerivative (repeatedFormalDerivative order coefficients)


repeatedFormalDerivative-zeroIteration : ∀ coefficients →
  repeatedFormalDerivative zero coefficients ≡ coefficients
repeatedFormalDerivative-zeroIteration coefficients = refl


repeatedFormalDerivative-successor : ∀ order coefficients →
  repeatedFormalDerivative (suc order) coefficients ≡
  formalDerivative (repeatedFormalDerivative order coefficients)
repeatedFormalDerivative-successor order coefficients = refl


repeatedFormalDerivative-add : ∀ order a b →
  repeatedFormalDerivative order (λ n → a n + b n) ≡
  (λ n →
    repeatedFormalDerivative order a n
      + repeatedFormalDerivative order b n)
repeatedFormalDerivative-add zero a b = refl
repeatedFormalDerivative-add (suc order) a b =
  cong formalDerivative
    (repeatedFormalDerivative-add order a b)
  ∙ formalDerivative-add
      (repeatedFormalDerivative order a)
      (repeatedFormalDerivative order b)


repeatedFormalDerivative-scale : ∀ order scalar coefficients →
  repeatedFormalDerivative order
      (scaleSeries scalar coefficients)
    ≡
  scaleSeries scalar
    (repeatedFormalDerivative order coefficients)
repeatedFormalDerivative-scale zero scalar coefficients = refl
repeatedFormalDerivative-scale (suc order) scalar coefficients =
  cong formalDerivative
    (repeatedFormalDerivative-scale order scalar coefficients)
  ∙ formalDerivative-scale scalar
      (repeatedFormalDerivative order coefficients)


repeatedFormalDerivative-zero : ∀ order →
  repeatedFormalDerivative order (λ _ → 0ℝ) ≡
  (λ _ → 0ℝ)
repeatedFormalDerivative-zero zero = refl
repeatedFormalDerivative-zero (suc order) =
  cong formalDerivative (repeatedFormalDerivative-zero order)
  ∙ formalDerivative-zero


repeatedFormalDerivative-addIterations : ∀ left right coefficients →
  repeatedFormalDerivative (left Nat.+ right) coefficients ≡
  repeatedFormalDerivative left
    (repeatedFormalDerivative right coefficients)
repeatedFormalDerivative-addIterations zero right coefficients = refl
repeatedFormalDerivative-addIterations
    (suc left) right coefficients =
  cong formalDerivative
    (repeatedFormalDerivative-addIterations
      left right coefficients)


-- The kth coefficient multiplier is (n + 1) · ... · (n + k).

derivativeNaturalProduct : ℕ → ℕ → ℕ
derivativeNaturalProduct index zero = 1
derivativeNaturalProduct index (suc order) =
  suc index Nat.· derivativeNaturalProduct (suc index) order


derivativeCoefficientIndex : ℕ → ℕ → ℕ
derivativeCoefficientIndex index zero = index
derivativeCoefficientIndex index (suc order) =
  derivativeCoefficientIndex (suc index) order


derivativeCoefficientIndex-add : ∀ index order →
  derivativeCoefficientIndex index order ≡ index Nat.+ order
derivativeCoefficientIndex-add index zero =
  sym (NatProperties.+-zero index)
derivativeCoefficientIndex-add index (suc order) =
  derivativeCoefficientIndex-add (suc index) order
  ∙ sym (NatProperties.+-suc index order)


repeatedFormalDerivative-coefficientWithIndex :
  ∀ order coefficients index →
  repeatedFormalDerivative order coefficients index ≡
  realNatural (derivativeNaturalProduct index order)
    · coefficients (derivativeCoefficientIndex index order)
repeatedFormalDerivative-coefficientWithIndex
    zero coefficients index =
  sym (mulIdL (coefficients index))
repeatedFormalDerivative-coefficientWithIndex
    (suc order) coefficients index =
  cong (realNatural (suc index) ·_)
    (repeatedFormalDerivative-coefficientWithIndex
      order coefficients (suc index))
  ∙ mulAssoc
      (realNatural (suc index))
      (realNatural
        (derivativeNaturalProduct (suc index) order))
      (coefficients
        (derivativeCoefficientIndex (suc index) order))
  ∙ cong
      (_· coefficients
        (derivativeCoefficientIndex (suc index) order))
      (sym
        (realNatural-mul
          (suc index)
          (derivativeNaturalProduct (suc index) order)))


repeatedFormalDerivative-coefficient :
  ∀ order coefficients index →
  repeatedFormalDerivative order coefficients index ≡
  realNatural (derivativeNaturalProduct index order)
    · coefficients (index Nat.+ order)
repeatedFormalDerivative-coefficient order coefficients index =
  repeatedFormalDerivative-coefficientWithIndex
    order coefficients index
  ∙ cong
      (realNatural (derivativeNaturalProduct index order) ·_)
      (cong coefficients
        (derivativeCoefficientIndex-add index order))
