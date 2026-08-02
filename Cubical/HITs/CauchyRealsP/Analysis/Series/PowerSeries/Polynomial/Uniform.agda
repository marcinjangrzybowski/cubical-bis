module Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Polynomial.Uniform where

open import Cubical.Foundations.Prelude

open import Cubical.Data.List
  using (List ; length)

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative
open import
  Cubical.HITs.CauchyRealsP.Analysis.Derivative.Polynomial
open import Cubical.HITs.CauchyRealsP.Analysis.Sequence
open import Cubical.HITs.CauchyRealsP.Analysis.Series.Base
open import Cubical.HITs.CauchyRealsP.Analysis.Series.Uniform
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Base
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Polynomial
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Uniform

open import Cubical.Relation.Premetric.Base

polynomialPowerSeriesUniformlyCauchyOnRadius :
  ∀ coefficients radius →
  PowerSeriesUniformlyCauchyOnRadius
    (polynomialCoefficientSequence coefficients)
    radius
polynomialPowerSeriesUniformlyCauchyOnRadius
  coefficients radius .fst ε =
    length coefficients
polynomialPowerSeriesUniformlyCauchyOnRadius
  coefficients radius .snd
  ε point m n length≤m length≤n =
    subst2 (_∼[ ε ]_)
      (sym
        (polynomialPowerSeriesPartialSumStableAbove
          coefficients (fst point) m length≤m))
      (sym
        (polynomialPowerSeriesPartialSumStableAbove
          coefficients (fst point) n length≤n))
      (refl∼ finite-sum ε)
  where
  finite-sum : ℝ
  finite-sum =
    partialSum
      (powerSeriesTerms
        (polynomialCoefficientSequence coefficients)
        (fst point))
      (length coefficients)

polynomialPowerSeriesFunctionOnClosedRadius :
  List ℝ →
  ∀ radius →
  ClosedAbsRadius radius →
  ℝ
polynomialPowerSeriesFunctionOnClosedRadius
  coefficients radius =
    powerSeriesUniformValueOnClosedRadius
      (polynomialCoefficientSequence coefficients)
      radius
      (polynomialPowerSeriesUniformlyCauchyOnRadius
        coefficients radius)

polynomialPowerSeriesFunctionOnClosedRadius-value :
  ∀ coefficients radius point →
  polynomialPowerSeriesFunctionOnClosedRadius
      coefficients radius point
    ≡
  evaluatePolynomial coefficients (fst point)
polynomialPowerSeriesFunctionOnClosedRadius-value
  coefficients radius point =
    polynomialPowerSeriesValue
      coefficients (fst point)
      (uniformlyCauchySeriesSummableAt
        (ClosedAbsRadius radius)
        (powerSeriesTermsOnClosedRadius
          (polynomialCoefficientSequence coefficients)
          radius)
        (polynomialPowerSeriesUniformlyCauchyOnRadius
          coefficients radius)
        point)

polynomialEvaluationHasDerivativeOnClosedRadius :
  ∀ coefficients radius →
  IsDerivativeAlong
    (snd (ClosedAbsRadiusPremetricSpace radius))
    fst
    (λ point →
      evaluatePolynomial coefficients (fst point))
    (λ point →
      evaluatePolynomialDerivative
        coefficients (fst point))
polynomialEvaluationHasDerivativeOnClosedRadius
  coefficients radius =
    evaluatePolynomialOfContinuousHasDerivativeAlong
      (snd (ClosedAbsRadiusPremetricSpace radius))
      fst
      (closedAbsRadiusCoordinateIsContinuous radius)
      coefficients

polynomialPowerSeriesFunctionHasDerivativeOnClosedRadius :
  ∀ coefficients radius →
  IsDerivativeAlong
    (snd (ClosedAbsRadiusPremetricSpace radius))
    fst
    (polynomialPowerSeriesFunctionOnClosedRadius
      coefficients radius)
    (λ point →
      evaluatePolynomialDerivative
        coefficients (fst point))
polynomialPowerSeriesFunctionHasDerivativeOnClosedRadius
  coefficients radius =
    subst
      (λ function →
        IsDerivativeAlong
          (snd (ClosedAbsRadiusPremetricSpace radius))
          fst function
          (λ point →
            evaluatePolynomialDerivative
              coefficients (fst point)))
      (sym
        (funExt
          (polynomialPowerSeriesFunctionOnClosedRadius-value
            coefficients radius)))
      (polynomialEvaluationHasDerivativeOnClosedRadius
        coefficients radius)
