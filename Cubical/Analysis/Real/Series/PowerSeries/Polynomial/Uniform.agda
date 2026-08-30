module Cubical.Analysis.Real.Series.PowerSeries.Polynomial.Uniform where

open import Cubical.Foundations.Prelude

open import Cubical.Data.List using (List ; length)

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Polynomial
open import Cubical.Analysis.Real.Domain.Radius
open import Cubical.Analysis.Real.Calculus.Derivative.Base
open import Cubical.Analysis.Real.Calculus.Derivative.Polynomial
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Uniform
open import Cubical.Analysis.Real.Series.PowerSeries.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Polynomial
open import Cubical.Analysis.Real.Series.PowerSeries.Difference.Derivative


-- Finite support gives a point-independent modulus: once both partial sums
-- are past the list length, they are definitionally equal to the same sum.

polynomialPowerSeriesChosenUniformlyCauchyOnRadius :
  ∀ coefficients radius →
  ChosenUniformlyCauchySeries
    (ClosedAbsRadius radius)
    (powerSeriesTermsOnClosedRadius
      (polynomialCoefficientSequence coefficients) radius)
polynomialPowerSeriesChosenUniformlyCauchyOnRadius
  coefficients radius .fst ε =
  length coefficients
polynomialPowerSeriesChosenUniformlyCauchyOnRadius
  coefficients radius .snd
  point ε m n length≤m length≤n =
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


polynomialPowerSeriesUniformlyCauchyOnRadius :
  ∀ coefficients radius →
  PowerSeriesUniformlyCauchyOnRadius
    (polynomialCoefficientSequence coefficients)
    radius
polynomialPowerSeriesUniformlyCauchyOnRadius coefficients radius =
  ∣ polynomialPowerSeriesChosenUniformlyCauchyOnRadius
      coefficients radius ∣₁


polynomialPowerSeriesFunctionOnClosedRadius :
  List ℝ → ∀ radius → ClosedAbsRadius radius → ℝ
polynomialPowerSeriesFunctionOnClosedRadius coefficients radius =
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
      (polynomialPowerSeriesUniformlyCauchyOnRadius
        coefficients radius)
      point)


polynomialEvaluationHasDerivativeOnClosedRadius :
  ∀ coefficients radius →
  IsDerivativeAlong
    (ClosedAbsRadiusPremetricSpace radius .snd)
    fst
    (λ point → evaluatePolynomial coefficients (fst point))
    (λ point →
      evaluatePolynomialDerivative coefficients (fst point))
polynomialEvaluationHasDerivativeOnClosedRadius
  coefficients radius =
  evaluatePolynomialHasDerivativeAlong
    (ClosedAbsRadiusPremetricSpace radius .snd)
    fst
    (closedAbsRadiusInclusionC radius .snd)
    coefficients
