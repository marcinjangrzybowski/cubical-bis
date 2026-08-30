module Cubical.Analysis.Real.Series.PowerSeries.Polynomial.Derivative where

open import Cubical.Foundations.Prelude

open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
import Cubical.Data.Nat as Nat

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Algebra.Natural
open import Cubical.Analysis.Real.Algebra.Polynomial
open import Cubical.Analysis.Real.Calculus.Derivative.Base
open import Cubical.Analysis.Real.Calculus.Derivative.Polynomial
open import Cubical.Analysis.Real.Domain.Radius
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Uniform
open import Cubical.Analysis.Real.Series.PowerSeries.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Derivative
open import Cubical.Analysis.Real.Series.PowerSeries.Polynomial
open import Cubical.Analysis.Real.Series.PowerSeries.Polynomial.Uniform
open import Cubical.Analysis.Real.Series.PowerSeries.Difference.Derivative


private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)


weightPolynomialCoefficients : ℕ → List ℝ → List ℝ
weightPolynomialCoefficients n [] = []
weightPolynomialCoefficients n (coefficient ∷ coefficients) =
  realNatural n · coefficient
  ∷ weightPolynomialCoefficients (suc n) coefficients


polynomialDerivativeCoefficients : List ℝ → List ℝ
polynomialDerivativeCoefficients [] = []
polynomialDerivativeCoefficients (constant ∷ coefficients) =
  weightPolynomialCoefficients (suc zero) coefficients


private
  commuteWeightedProduct : ∀ (a b c : ℝ) →
    a · (b · c) ≡ b · (a · c)
  commuteWeightedProduct a b c =
    mulAssoc a b c
    ∙ cong (_· c) (mulComm a b)
    ∙ sym (mulAssoc b a c)

  weightedPolynomialStep :
    ∀ (n coefficient x tail derivative-tail : ℝ) →
    n · coefficient
        + x · ((n + 1ℝ) · tail + x · derivative-tail)
      ≡
    n · (coefficient + x · tail)
      + x · (tail + x · derivative-tail)
  weightedPolynomialStep n coefficient x tail derivative-tail =
    cong
      (n · coefficient +_)
      (cong
        (x ·_)
        (cong
          (_+ x · derivative-tail)
          ( mulDistL n 1ℝ tail
          ∙ cong (n · tail +_) (mulIdL tail))))
    ∙ cong
        (n · coefficient +_)
        (mulDistR x (n · tail + tail) (x · derivative-tail))
    ∙ cong
        (n · coefficient +_)
        (cong
          (_+ x · (x · derivative-tail))
          (mulDistR x (n · tail) tail))
    ∙ addAssoc
        (n · coefficient)
        (x · (n · tail) + x · tail)
        (x · (x · derivative-tail))
    ∙ cong
        (_+ x · (x · derivative-tail))
        (addAssoc
          (n · coefficient)
          (x · (n · tail))
          (x · tail))
    ∙ cong
        (λ value →
          ((n · coefficient + value) + x · tail)
            + x · (x · derivative-tail))
        (commuteWeightedProduct x n tail)
    ∙ sym
        (addAssoc
          (n · coefficient + n · (x · tail))
          (x · tail)
          (x · (x · derivative-tail)))
    ∙ cong₂ _+_
        (sym (mulDistR n coefficient (x · tail)))
        (sym (mulDistR x tail (x · derivative-tail)))


weightPolynomialEvaluation : ∀ n coefficients x →
  evaluatePolynomial
      (weightPolynomialCoefficients n coefficients) x
    ≡
  realNatural n · evaluatePolynomial coefficients x
    + x · evaluatePolynomialDerivative coefficients x
weightPolynomialEvaluation n [] x =
  sym
    ( cong₂ _+_
        (ℝRing.0RightAnnihilates (realNatural n))
        (ℝRing.0RightAnnihilates x)
    ∙ addIdL 0ℝ)
weightPolynomialEvaluation n (coefficient ∷ coefficients) x =
  cong
    (λ value → realNatural n · coefficient + x · value)
    (weightPolynomialEvaluation (suc n) coefficients x)
  ∙ cong
      (realNatural n · coefficient +_)
      (cong
        (x ·_)
        (cong
          (_+ x · evaluatePolynomialDerivative coefficients x)
          (cong
            (_· evaluatePolynomial coefficients x)
            (realNatural-suc n))))
  ∙ weightedPolynomialStep
      (realNatural n) coefficient x
      (evaluatePolynomial coefficients x)
      (evaluatePolynomialDerivative coefficients x)


evaluatePolynomialDerivativeCoefficients : ∀ coefficients x →
  evaluatePolynomial
      (polynomialDerivativeCoefficients coefficients) x
    ≡
  evaluatePolynomialDerivative coefficients x
evaluatePolynomialDerivativeCoefficients [] x = refl
evaluatePolynomialDerivativeCoefficients
  (constant ∷ coefficients) x =
  weightPolynomialEvaluation (suc zero) coefficients x
  ∙ cong
      (_+ x · evaluatePolynomialDerivative coefficients x)
      ( cong
          (_· evaluatePolynomial coefficients x)
          (addIdL 1ℝ)
      ∙ mulIdL (evaluatePolynomial coefficients x))


weightPolynomialCoefficientSequence :
  ∀ start coefficients n →
  polynomialCoefficientSequence
      (weightPolynomialCoefficients start coefficients) n
    ≡
  realNatural (start Nat.+ n) ·
    polynomialCoefficientSequence coefficients n
weightPolynomialCoefficientSequence start [] n =
  sym (ℝRing.0RightAnnihilates (realNatural (start Nat.+ n)))
weightPolynomialCoefficientSequence
  start (coefficient ∷ coefficients) zero =
  cong
    (_· coefficient)
    (cong realNatural (sym (Nat.+-zero start)))
weightPolynomialCoefficientSequence
  start (coefficient ∷ coefficients) (suc n) =
  weightPolynomialCoefficientSequence (suc start) coefficients n
  ∙ cong
      (_· polynomialCoefficientSequence coefficients n)
      (cong realNatural (sym (Nat.+-suc start n)))


formalDerivativePolynomialCoefficientSequence :
  ∀ coefficients →
  formalDerivative (polynomialCoefficientSequence coefficients)
    ≡
  polynomialCoefficientSequence
    (polynomialDerivativeCoefficients coefficients)
formalDerivativePolynomialCoefficientSequence [] =
  funExt
    (λ n → ℝRing.0RightAnnihilates (realNatural (suc n)))
formalDerivativePolynomialCoefficientSequence
  (constant ∷ coefficients) =
  funExt
    (λ n →
      sym
        (weightPolynomialCoefficientSequence
          (suc zero) coefficients n))


polynomialFormalDerivativePowerSeriesValue :
  ∀ coefficients x →
  (summable :
    PowerSeriesSummableAt
      (formalDerivative
        (polynomialCoefficientSequence coefficients)) x) →
  powerSeriesValue
      (formalDerivative
        (polynomialCoefficientSequence coefficients))
      x summable
    ≡
  evaluatePolynomialDerivative coefficients x
polynomialFormalDerivativePowerSeriesValue
  coefficients x summable =
  seriesSumPresPath
    formal-terms polynomial-terms terms-path
    summable
    (polynomialPowerSeriesSummable derivative-coefficients x)
  ∙ polynomialPowerSeriesValue
      derivative-coefficients x
      (polynomialPowerSeriesSummable derivative-coefficients x)
  ∙ evaluatePolynomialDerivativeCoefficients coefficients x
  where
  derivative-coefficients : List ℝ
  derivative-coefficients =
    polynomialDerivativeCoefficients coefficients

  formal-terms polynomial-terms : RealSequence
  formal-terms =
    powerSeriesTerms
      (formalDerivative
        (polynomialCoefficientSequence coefficients)) x
  polynomial-terms =
    powerSeriesTerms
      (polynomialCoefficientSequence derivative-coefficients) x

  terms-path : formal-terms ≡ polynomial-terms
  terms-path =
    cong
      (λ coefficient-sequence →
        powerSeriesTerms coefficient-sequence x)
      (formalDerivativePolynomialCoefficientSequence coefficients)


polynomialFormalDerivativeUniformlyCauchyOnRadius :
  ∀ coefficients radius →
  FormalDerivativePowerSeriesUniformlyCauchyOnRadius
    (polynomialCoefficientSequence coefficients) radius
polynomialFormalDerivativeUniformlyCauchyOnRadius
  coefficients radius =
  subst
    (λ coefficient-sequence →
      PowerSeriesUniformlyCauchyOnRadius
        coefficient-sequence radius)
    (sym
      (formalDerivativePolynomialCoefficientSequence coefficients))
    (polynomialPowerSeriesUniformlyCauchyOnRadius
      (polynomialDerivativeCoefficients coefficients) radius)


polynomialFormalDerivativePowerSeriesFunctionOnClosedRadius :
  List ℝ → ∀ radius → ClosedAbsRadius radius → ℝ
polynomialFormalDerivativePowerSeriesFunctionOnClosedRadius
  coefficients radius =
  formalDerivativePowerSeriesUniformValueOnClosedRadius
    (polynomialCoefficientSequence coefficients)
    radius
    (polynomialFormalDerivativeUniformlyCauchyOnRadius
      coefficients radius)


polynomialFormalDerivativePowerSeriesFunctionOnClosedRadius-value :
  ∀ coefficients radius point →
  polynomialFormalDerivativePowerSeriesFunctionOnClosedRadius
      coefficients radius point
    ≡
  evaluatePolynomialDerivative coefficients (fst point)
polynomialFormalDerivativePowerSeriesFunctionOnClosedRadius-value
  coefficients radius point =
  polynomialFormalDerivativePowerSeriesValue
    coefficients (fst point)
    (uniformlyCauchySeriesSummableAt
      (polynomialFormalDerivativeUniformlyCauchyOnRadius
        coefficients radius)
      point)


-- The formal derivative series and the Horner derivative commute on every
-- closed radius.  Keeping Horner as the source function avoids transporting
-- the substantially larger canonical-series derivative proof.

polynomialEvaluationHasFormalDerivativeOnClosedRadius :
  ∀ coefficients radius →
  IsDerivativeAlong
    (ClosedAbsRadiusPremetricSpace radius .snd)
    fst
    (λ point → evaluatePolynomial coefficients (fst point))
    (polynomialFormalDerivativePowerSeriesFunctionOnClosedRadius
      coefficients radius)
polynomialEvaluationHasFormalDerivativeOnClosedRadius
  coefficients radius =
  subst
    (λ derivative →
      IsDerivativeAlong
        (ClosedAbsRadiusPremetricSpace radius .snd)
        fst
        (λ point → evaluatePolynomial coefficients (fst point))
        derivative)
    (sym
      (funExt
        (polynomialFormalDerivativePowerSeriesFunctionOnClosedRadius-value
          coefficients radius)))
    (polynomialEvaluationHasDerivativeOnClosedRadius
      coefficients radius)
