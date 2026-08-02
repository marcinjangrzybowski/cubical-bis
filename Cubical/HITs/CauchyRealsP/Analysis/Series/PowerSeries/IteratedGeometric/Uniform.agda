module Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.IteratedGeometric.Uniform where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat
  using (ℕ ; suc)
import Cubical.Data.Rationals as ℚ

open import Cubical.Relation.Premetric.Mappings

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Derivative
open import Cubical.HITs.CauchyRealsP.Analysis.Sequence
open import Cubical.HITs.CauchyRealsP.Analysis.Series.Base
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Absolute
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Operations
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Uniform
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Geometric.Comparison
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Base
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Operations
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Majorant
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Uniform
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Derivative
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Difference.Uniform
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Difference.Derivative
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.IteratedGeometric
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.IteratedGeometric.Coefficients
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.IteratedGeometric.Derivative

iteratedGeometricPowerSeriesUniformlyAbsolutelyCauchy :
  ∀ radius →
  RationalContractionBound radius →
  ∀ order →
  PowerSeriesUniformlyAbsolutelyCauchyOnRadius
    (iteratedGeometricCoefficients
      order)
    radius
iteratedGeometricPowerSeriesUniformlyAbsolutelyCauchy
  radius contraction order =
    powerSeriesUniformlyAbsolutelyCauchyByCoefficientMajorant
      coefficients coefficients radius
      (nonnegativeCoefficientsSelfMajorized
        coefficients nonnegative)
      nonnegative
      (absoluteCauchySeriesIsCauchy
        (powerSeriesTerms coefficients radius)
        (iteratedGeometricPowerSeriesIsAbsolutelyCauchy
          radius contraction order))
  where
  coefficients : RealSequence
  coefficients =
    iteratedGeometricCoefficients
      order

  nonnegative :
    NonnegativeCoefficients coefficients
  nonnegative =
    iteratedGeometricCoefficients-nonnegative
      order

iteratedGeometricPowerSeriesUniformlyCauchy :
  ∀ radius →
  RationalContractionBound radius →
  ∀ order →
  PowerSeriesUniformlyCauchyOnRadius
    (iteratedGeometricCoefficients
      order)
    radius
iteratedGeometricPowerSeriesUniformlyCauchy
  radius contraction order =
    powerSeriesUniformlyCauchyByCoefficientMajorant
      coefficients coefficients radius
      (nonnegativeCoefficientsSelfMajorized
        coefficients nonnegative)
      nonnegative
      (absoluteCauchySeriesIsCauchy
        (powerSeriesTerms coefficients radius)
        (iteratedGeometricPowerSeriesIsAbsolutelyCauchy
          radius contraction order))
  where
  coefficients : RealSequence
  coefficients =
    iteratedGeometricCoefficients
      order

  nonnegative :
    NonnegativeCoefficients coefficients
  nonnegative =
    iteratedGeometricCoefficients-nonnegative
      order

iteratedGeometricFormalDerivativePowerSeriesIsAbsolutelyCauchy :
  ∀ radius →
  RationalContractionBound radius →
  ∀ order →
  IsAbsolutelyCauchySeries
    (powerSeriesTerms
      (formalDerivative
        (iteratedGeometricCoefficients
          order))
      radius)
iteratedGeometricFormalDerivativePowerSeriesIsAbsolutelyCauchy
  radius contraction order =
    subst
      IsAbsolutelyCauchySeries
      (sym derivative-terms-path)
      (rationalScaleSeriesIsAbsolutelyCauchy
        (ℚ.fromNat (suc order))
        next-terms
        (iteratedGeometricPowerSeriesIsAbsolutelyCauchy
          radius contraction (suc order)))
  where
  next-coefficients : RealSequence
  next-coefficients =
    iteratedGeometricCoefficients
      (suc order)

  next-terms : RealSequence
  next-terms =
    powerSeriesTerms
      next-coefficients radius

  derivative-terms-path :
    powerSeriesTerms
        (formalDerivative
          (iteratedGeometricCoefficients
            order))
        radius
      ≡
    scaleSeries
      (rat (ℚ.fromNat (suc order)))
      next-terms
  derivative-terms-path =
    cong
      (λ coefficients →
        powerSeriesTerms coefficients radius)
      (formalDerivative-iteratedGeometric
        order)
    ∙ powerSeriesTerms-scale-sequence
        (realNatural (suc order))
        next-coefficients radius
    ∙ cong
        (λ coefficient →
          scaleSeries coefficient next-terms)
        (realNatural-rat (suc order))

iteratedGeometricFormalDerivativeCoefficients-nonnegative :
  ∀ order →
  NonnegativeCoefficients
    (formalDerivative
      (iteratedGeometricCoefficients
        order))
iteratedGeometricFormalDerivativeCoefficients-nonnegative
  order n =
    subst
      (0 ≤ℝ_)
      (sym
        (formalDerivative-iteratedGeometric-pointwise
          order n))
      (mulNonnegative
        (realNatural (suc order))
        (iteratedGeometricCoefficients
          (suc order) n)
        (realNatural-nonnegative
          (suc order))
        (iteratedGeometricCoefficients-nonnegative
          (suc order) n))

iteratedGeometricFormalDerivativePowerSeriesUniformlyAbsolutelyCauchy :
  ∀ radius →
  RationalContractionBound radius →
  ∀ order →
  PowerSeriesUniformlyAbsolutelyCauchyOnRadius
    (formalDerivative
      (iteratedGeometricCoefficients
        order))
    radius
iteratedGeometricFormalDerivativePowerSeriesUniformlyAbsolutelyCauchy
  radius contraction order =
    powerSeriesUniformlyAbsolutelyCauchyByCoefficientMajorant
      coefficients coefficients radius
      (nonnegativeCoefficientsSelfMajorized
        coefficients nonnegative)
      nonnegative
      (absoluteCauchySeriesIsCauchy
        (powerSeriesTerms coefficients radius)
        (iteratedGeometricFormalDerivativePowerSeriesIsAbsolutelyCauchy
          radius contraction order))
  where
  coefficients : RealSequence
  coefficients =
    formalDerivative
      (iteratedGeometricCoefficients
        order)

  nonnegative :
    NonnegativeCoefficients coefficients
  nonnegative =
    iteratedGeometricFormalDerivativeCoefficients-nonnegative
      order

iteratedGeometricFormalDerivativePowerSeriesUniformlyCauchy :
  ∀ radius →
  RationalContractionBound radius →
  ∀ order →
  PowerSeriesUniformlyCauchyOnRadius
    (formalDerivative
      (iteratedGeometricCoefficients
        order))
    radius
iteratedGeometricFormalDerivativePowerSeriesUniformlyCauchy
  radius contraction order =
    powerSeriesUniformlyCauchyByCoefficientMajorant
      coefficients coefficients radius
      (nonnegativeCoefficientsSelfMajorized
        coefficients nonnegative)
      nonnegative
      (absoluteCauchySeriesIsCauchy
        (powerSeriesTerms coefficients radius)
        (iteratedGeometricFormalDerivativePowerSeriesIsAbsolutelyCauchy
          radius contraction order))
  where
  coefficients : RealSequence
  coefficients =
    formalDerivative
      (iteratedGeometricCoefficients
        order)

  nonnegative :
    NonnegativeCoefficients coefficients
  nonnegative =
    iteratedGeometricFormalDerivativeCoefficients-nonnegative
      order

iteratedGeometricPowerSeriesFunctionOnClosedRadius :
  ∀ radius →
  RationalContractionBound radius →
  ℕ →
  ClosedAbsRadius radius →
  ℝ
iteratedGeometricPowerSeriesFunctionOnClosedRadius
  radius contraction order =
    powerSeriesUniformValueOnClosedRadius
      (iteratedGeometricCoefficients
        order)
      radius
      (iteratedGeometricPowerSeriesUniformlyCauchy
        radius contraction order)

iteratedGeometricPowerSeriesFunctionOnClosedRadiusIsContinuous :
  ∀ radius →
  (contraction :
    RationalContractionBound radius) →
  ∀ order →
  isContinuous
    (snd
      (ClosedAbsRadiusPremetricSpace
        radius))
    (iteratedGeometricPowerSeriesFunctionOnClosedRadius
      radius contraction order)
    (snd ℝPremetricSpace)
iteratedGeometricPowerSeriesFunctionOnClosedRadiusIsContinuous
  radius contraction order =
    powerSeriesUniformValueOnClosedRadiusIsContinuous
      (iteratedGeometricCoefficients
        order)
      radius
      (iteratedGeometricPowerSeriesUniformlyCauchy
        radius contraction order)

iteratedGeometricFormalDerivativePowerSeriesFunctionOnClosedRadius :
  ∀ radius →
  RationalContractionBound radius →
  ℕ →
  ClosedAbsRadius radius →
  ℝ
iteratedGeometricFormalDerivativePowerSeriesFunctionOnClosedRadius
  radius contraction order =
    powerSeriesUniformValueOnClosedRadius
      (formalDerivative
        (iteratedGeometricCoefficients
          order))
      radius
      (iteratedGeometricFormalDerivativePowerSeriesUniformlyCauchy
        radius contraction order)

iteratedGeometricFormalDerivativePowerSeriesFunctionOnClosedRadiusIsContinuous :
  ∀ radius →
  (contraction :
    RationalContractionBound radius) →
  ∀ order →
  isContinuous
    (snd
      (ClosedAbsRadiusPremetricSpace
        radius))
    (iteratedGeometricFormalDerivativePowerSeriesFunctionOnClosedRadius
      radius contraction order)
    (snd ℝPremetricSpace)
iteratedGeometricFormalDerivativePowerSeriesFunctionOnClosedRadiusIsContinuous
  radius contraction order =
    powerSeriesUniformValueOnClosedRadiusIsContinuous
      (formalDerivative
        (iteratedGeometricCoefficients
          order))
      radius
      (iteratedGeometricFormalDerivativePowerSeriesUniformlyCauchy
        radius contraction order)

iteratedGeometricPowerSeriesDifferenceFactorUniformlyCauchy :
  ∀ radius →
  RationalContractionBound radius →
  ∀ order →
  PowerSeriesDifferenceFactorUniformlyCauchyOnRadius
    (iteratedGeometricCoefficients order)
    radius
iteratedGeometricPowerSeriesDifferenceFactorUniformlyCauchy
  radius contraction order =
    powerSeriesDifferenceFactorUniformlyCauchyByDerivativeMajorant
      coefficients coefficients radius
      (nonnegativeCoefficientsSelfMajorized
        coefficients nonnegative)
      nonnegative
      (absoluteCauchySeriesIsCauchy
        (powerSeriesTerms
          (formalDerivativeMajorant coefficients)
          radius)
        (iteratedGeometricFormalDerivativePowerSeriesIsAbsolutelyCauchy
          radius contraction order))
  where
  coefficients : RealSequence
  coefficients =
    iteratedGeometricCoefficients order

  nonnegative :
    NonnegativeCoefficients coefficients
  nonnegative =
    iteratedGeometricCoefficients-nonnegative
      order

iteratedGeometricPowerSeriesFunctionHasFormalDerivativeOnClosedRadius :
  ∀ radius →
  (contraction : RationalContractionBound radius) →
  ∀ order →
  IsDerivativeAlong
    (snd (ClosedAbsRadiusPremetricSpace radius))
    fst
    (iteratedGeometricPowerSeriesFunctionOnClosedRadius
      radius contraction order)
    (iteratedGeometricFormalDerivativePowerSeriesFunctionOnClosedRadius
      radius contraction order)
iteratedGeometricPowerSeriesFunctionHasFormalDerivativeOnClosedRadius
  radius contraction order =
    powerSeriesUniformValueHasFormalDerivativeOnClosedRadius
      (iteratedGeometricCoefficients order)
      radius
      (iteratedGeometricPowerSeriesUniformlyCauchy
        radius contraction order)
      (iteratedGeometricFormalDerivativePowerSeriesUniformlyCauchy
        radius contraction order)
      (iteratedGeometricPowerSeriesDifferenceFactorUniformlyCauchy
        radius contraction order)

closedRadiusPointContraction :
  ∀ radius →
  RationalContractionBound radius →
  (point : ClosedAbsRadius radius) →
  RationalContractionBound (fst point)
closedRadiusPointContraction
  radius contraction point =
    rationalContractionBoundWithin
      (fst point) radius
      (snd point) contraction

iteratedGeometricClosedFormOnClosedRadius :
  ∀ radius →
  (contraction : RationalContractionBound radius) →
  ℕ →
  ClosedAbsRadius radius →
  ℝ
iteratedGeometricClosedFormOnClosedRadius
  radius contraction order point =
    iteratedProduct order
      (positiveReciprocal
        (1 - fst point)
        (positiveSub (fst point) 1
          (rationalContractionBound→x<1
            (fst point)
            (closedRadiusPointContraction
              radius contraction point))))

iteratedGeometricClosedFormDerivativeOnClosedRadius :
  ∀ radius →
  (contraction : RationalContractionBound radius) →
  ℕ →
  ClosedAbsRadius radius →
  ℝ
iteratedGeometricClosedFormDerivativeOnClosedRadius
  radius contraction order point =
    realNatural (suc order)
      · iteratedProduct (suc order)
          (positiveReciprocal
            (1 - fst point)
            (positiveSub (fst point) 1
              (rationalContractionBound→x<1
                (fst point)
                (closedRadiusPointContraction
                  radius contraction point))))

iteratedGeometricPowerSeriesFunctionOnClosedRadius-value :
  ∀ radius →
  (contraction : RationalContractionBound radius) →
  ∀ order point →
  iteratedGeometricPowerSeriesFunctionOnClosedRadius
      radius contraction order point
    ≡
  iteratedGeometricClosedFormOnClosedRadius
    radius contraction order point
iteratedGeometricPowerSeriesFunctionOnClosedRadius-value
  radius contraction order point =
    iteratedGeometricPowerSeriesValue
      (fst point)
      (closedRadiusPointContraction
        radius contraction point)
      order
      (uniformlyCauchySeriesSummableAt
        (ClosedAbsRadius radius)
        (powerSeriesTermsOnClosedRadius
          (iteratedGeometricCoefficients order)
          radius)
        (iteratedGeometricPowerSeriesUniformlyCauchy
          radius contraction order)
        point)

iteratedGeometricFormalDerivativePowerSeriesFunctionOnClosedRadius-value :
  ∀ radius →
  (contraction : RationalContractionBound radius) →
  ∀ order point →
  iteratedGeometricFormalDerivativePowerSeriesFunctionOnClosedRadius
      radius contraction order point
    ≡
  iteratedGeometricClosedFormDerivativeOnClosedRadius
    radius contraction order point
iteratedGeometricFormalDerivativePowerSeriesFunctionOnClosedRadius-value
  radius contraction order point =
    iteratedGeometricFormalDerivativePowerSeriesValue
      (fst point)
      (closedRadiusPointContraction
        radius contraction point)
      order
      (uniformlyCauchySeriesSummableAt
        (ClosedAbsRadius radius)
        (powerSeriesTermsOnClosedRadius
          (formalDerivative
            (iteratedGeometricCoefficients order))
          radius)
        (iteratedGeometricFormalDerivativePowerSeriesUniformlyCauchy
          radius contraction order)
        point)

iteratedGeometricClosedFormHasDerivativeOnClosedRadius :
  ∀ radius →
  (contraction : RationalContractionBound radius) →
  ∀ order →
  IsDerivativeAlong
    (snd (ClosedAbsRadiusPremetricSpace radius))
    fst
    (iteratedGeometricClosedFormOnClosedRadius
      radius contraction order)
    (iteratedGeometricClosedFormDerivativeOnClosedRadius
      radius contraction order)
iteratedGeometricClosedFormHasDerivativeOnClosedRadius
  radius contraction order =
    subst2
      (IsDerivativeAlong
        (snd (ClosedAbsRadiusPremetricSpace radius))
        fst)
      (funExt
        (iteratedGeometricPowerSeriesFunctionOnClosedRadius-value
          radius contraction order))
      (funExt
        (iteratedGeometricFormalDerivativePowerSeriesFunctionOnClosedRadius-value
          radius contraction order))
      (iteratedGeometricPowerSeriesFunctionHasFormalDerivativeOnClosedRadius
        radius contraction order)
