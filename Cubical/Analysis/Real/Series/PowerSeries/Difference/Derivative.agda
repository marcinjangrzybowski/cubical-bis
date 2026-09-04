module Cubical.Analysis.Real.Series.PowerSeries.Difference.Derivative where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Domain.Radius
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Uniform
open import Cubical.Analysis.Real.Series.PowerSeries.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Majorant
open import Cubical.Analysis.Real.Series.PowerSeries.Derivative
open import Cubical.Analysis.Real.Series.PowerSeries.Difference
open import Cubical.Analysis.Real.Series.PowerSeries.Difference.Sum
open import Cubical.Analysis.Real.Series.PowerSeries.Difference.Uniform
open import Cubical.Analysis.Real.Calculus.Derivative.Base


powerSeriesTermsOnClosedRadius :
  RealSequence → ∀ radius →
  ClosedAbsRadius radius → RealSequence
powerSeriesTermsOnClosedRadius coefficients radius point =
  powerSeriesTerms coefficients (fst point)


PowerSeriesUniformlyCauchyOnRadius :
  RealSequence → ℝ → Type₀
PowerSeriesUniformlyCauchyOnRadius coefficients radius =
  UniformlyCauchySeries
    (ClosedAbsRadius radius)
    (powerSeriesTermsOnClosedRadius coefficients radius)


powerSeriesUniformlyCauchyOnSmallerRadius :
  ∀ coefficients radius larger →
  radius ≤ℝ larger →
  PowerSeriesUniformlyCauchyOnRadius coefficients larger →
  PowerSeriesUniformlyCauchyOnRadius coefficients radius
powerSeriesUniformlyCauchyOnSmallerRadius
    coefficients radius larger radius≤larger uniform =
  uniformlyCauchySeriesPrecompose
    (powerSeriesTermsOnClosedRadius coefficients larger)
    (fst (closedAbsRadiusMonotoneNE radius larger radius≤larger))
    uniform


powerSeriesUniformValueOnClosedRadius :
  ∀ coefficients radius →
  PowerSeriesUniformlyCauchyOnRadius coefficients radius →
  ClosedAbsRadius radius → ℝ
powerSeriesUniformValueOnClosedRadius
  coefficients radius uniform =
  uniformSeriesValue
    (powerSeriesTermsOnClosedRadius coefficients radius)
    uniform


FormalDerivativePowerSeriesUniformlyCauchyOnRadius :
  RealSequence → ℝ → Type₀
FormalDerivativePowerSeriesUniformlyCauchyOnRadius
  coefficients radius =
  PowerSeriesUniformlyCauchyOnRadius
    (formalDerivative coefficients) radius


formalDerivativePowerSeriesUniformValueOnClosedRadius :
  ∀ coefficients radius →
  FormalDerivativePowerSeriesUniformlyCauchyOnRadius
    coefficients radius →
  ClosedAbsRadius radius → ℝ
formalDerivativePowerSeriesUniformValueOnClosedRadius
  coefficients radius derivative-uniform =
  powerSeriesUniformValueOnClosedRadius
    (formalDerivative coefficients) radius derivative-uniform


powerSeriesDifferenceFactorValueOnClosedRadius :
  ∀ coefficients radius →
  PowerSeriesDifferenceFactorUniformlyCauchyOnRadius
    coefficients radius →
  ClosedAbsRadiusPair radius → ℝ
powerSeriesDifferenceFactorValueOnClosedRadius
  coefficients radius factor-uniform =
  uniformSeriesValue
    (powerSeriesDifferenceFactorOnClosedRadius
      coefficients radius)
    factor-uniform


powerSeriesDifferenceFactorValueOnClosedRadiusIsContinuous :
  ∀ coefficients radius
    (factor-uniform :
      PowerSeriesDifferenceFactorUniformlyCauchyOnRadius
        coefficients radius) →
  isContinuous
    (ClosedAbsRadiusPairPremetricSpace radius .snd)
    (powerSeriesDifferenceFactorValueOnClosedRadius
      coefficients radius factor-uniform)
    (ℝPremetricSpace .snd)
powerSeriesDifferenceFactorValueOnClosedRadiusIsContinuous
  coefficients radius factor-uniform =
  uniformSeriesValueIsContinuous
    (ClosedAbsRadiusPairPremetricSpace radius .snd)
    (powerSeriesDifferenceFactorOnClosedRadius
      coefficients radius)
    factor-uniform
    (powerSeriesDifferenceFactorTermOnClosedRadiusIsContinuous
      coefficients radius)


powerSeriesUniformValueHasFormalDerivativeOnClosedRadius :
  ∀ coefficients radius →
  (uniform :
    PowerSeriesUniformlyCauchyOnRadius
      coefficients radius) →
  (derivative-uniform :
    FormalDerivativePowerSeriesUniformlyCauchyOnRadius
      coefficients radius) →
  (factor-uniform :
    PowerSeriesDifferenceFactorUniformlyCauchyOnRadius
      coefficients radius) →
  IsDerivativeAlong
    (ClosedAbsRadiusPremetricSpace radius .snd)
    fst
    (powerSeriesUniformValueOnClosedRadius
      coefficients radius uniform)
    (formalDerivativePowerSeriesUniformValueOnClosedRadius
      coefficients radius derivative-uniform)
powerSeriesUniformValueHasFormalDerivativeOnClosedRadius
  coefficients radius
  uniform derivative-uniform factor-uniform =
  continuousDifferenceFactorGivesDerivative
    (ClosedAbsRadiusPremetricSpace radius .snd)
    fst
    (powerSeriesUniformValueOnClosedRadius
      coefficients radius uniform)
    (formalDerivativePowerSeriesUniformValueOnClosedRadius
      coefficients radius derivative-uniform)
    (powerSeriesDifferenceFactorValueOnClosedRadius
      coefficients radius factor-uniform)
    factorization
    diagonal
    (powerSeriesDifferenceFactorValueOnClosedRadiusIsContinuous
      coefficients radius factor-uniform)
  where
  original-summable : ∀ point →
    PowerSeriesSummableAt coefficients (fst point)
  original-summable point =
    uniformlyCauchySeriesSummableAt uniform point

  derivative-summable : ∀ point →
    PowerSeriesSummableAt
      (formalDerivative coefficients) (fst point)
  derivative-summable point =
    uniformlyCauchySeriesSummableAt
      derivative-uniform point

  factor-summable : ∀ point →
    Summable
      (powerSeriesDifferenceFactorOnClosedRadius
        coefficients radius point)
  factor-summable point =
    uniformlyCauchySeriesSummableAt
      factor-uniform point

  factorization : ∀ x y →
    powerSeriesUniformValueOnClosedRadius
        coefficients radius uniform y
      -
    powerSeriesUniformValueOnClosedRadius
        coefficients radius uniform x
      ≡
    (fst y - fst x) ·
      powerSeriesDifferenceFactorValueOnClosedRadius
        coefficients radius factor-uniform (x , y)
  factorization x y =
    powerSeriesValueDifferenceFactorization
      coefficients (fst x) (fst y)
      (original-summable x)
      (original-summable y)
      (factor-summable (x , y))

  diagonal : ∀ x →
    powerSeriesDifferenceFactorValueOnClosedRadius
        coefficients radius factor-uniform (x , x)
      ≡
    formalDerivativePowerSeriesUniformValueOnClosedRadius
      coefficients radius derivative-uniform x
  diagonal x =
    powerSeriesDifferenceFactorDiagonalValue
      coefficients (fst x)
      (factor-summable (x , x))
      (derivative-summable x)


formalDerivativePowerSeriesUniformlyCauchyByCoefficientMajorant :
  ∀ coefficients majorant radius →
  CoefficientMajorizedBy coefficients majorant →
  IsCauchySeries
    (powerSeriesTerms
      (formalDerivativeMajorant majorant) radius) →
  FormalDerivativePowerSeriesUniformlyCauchyOnRadius
    coefficients radius
formalDerivativePowerSeriesUniformlyCauchyByCoefficientMajorant
  coefficients majorant radius
  majorized derivative-majorant-cauchy =
  uniformlyDominatedSeriesIsUniformlyCauchy
    (powerSeriesTermsOnClosedRadius
      (formalDerivative coefficients) radius)
    (powerSeriesTerms
      (formalDerivativeMajorant majorant) radius)
    dominates
    derivative-majorant-cauchy
  where
  derivative-majorized :
    CoefficientMajorizedBy
      (formalDerivative coefficients)
      (formalDerivativeMajorant majorant)
  derivative-majorized =
    formalDerivativePresCoefficientMajorant
      coefficients majorant majorized

  dominates : ∀ point n →
    absℝ
      (powerSeriesTermsOnClosedRadius
        (formalDerivative coefficients) radius point n)
      ≤ℝ
    powerSeriesTerms
      (formalDerivativeMajorant majorant) radius n
  dominates point =
    powerSeriesTermAbsBoundByCoefficientMajorant
      (formalDerivative coefficients)
      (formalDerivativeMajorant majorant)
      (fst point) radius
      derivative-majorized
      (snd point)


powerSeriesUniformValueHasFormalDerivativeByMajorant :
  ∀ coefficients majorant radius →
  (majorized :
    CoefficientMajorizedBy coefficients majorant) →
  (uniform :
    PowerSeriesUniformlyCauchyOnRadius
      coefficients radius) →
  (derivative-majorant-cauchy :
    IsCauchySeries
      (powerSeriesTerms
        (formalDerivativeMajorant majorant) radius)) →
  IsDerivativeAlong
    (ClosedAbsRadiusPremetricSpace radius .snd)
    fst
    (powerSeriesUniformValueOnClosedRadius
      coefficients radius uniform)
    (formalDerivativePowerSeriesUniformValueOnClosedRadius
      coefficients radius
      (formalDerivativePowerSeriesUniformlyCauchyByCoefficientMajorant
        coefficients majorant radius
        majorized derivative-majorant-cauchy))
powerSeriesUniformValueHasFormalDerivativeByMajorant
  coefficients majorant radius
  majorized uniform derivative-majorant-cauchy =
  powerSeriesUniformValueHasFormalDerivativeOnClosedRadius
    coefficients radius uniform
    (formalDerivativePowerSeriesUniformlyCauchyByCoefficientMajorant
      coefficients majorant radius
      majorized derivative-majorant-cauchy)
    (powerSeriesDifferenceFactorUniformlyCauchyByDerivativeMajorant
      coefficients majorant radius
      majorized derivative-majorant-cauchy)
