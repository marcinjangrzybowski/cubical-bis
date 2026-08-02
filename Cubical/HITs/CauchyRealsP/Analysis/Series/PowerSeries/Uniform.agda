module Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Uniform where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset

open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation.Monad

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Sequence
open import Cubical.HITs.CauchyRealsP.Analysis.Series.Base
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Absolute
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Uniform
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Base
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Majorant
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Convergence
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Derivative
open import
  Cubical.HITs.CauchyRealsP.Analysis.Metric.Radius public

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

powerSeriesTermsOnClosedRadius :
  RealSequence →
  ∀ radius →
  ClosedAbsRadius radius →
  RealSequence
powerSeriesTermsOnClosedRadius
  coefficients radius point =
    powerSeriesTerms
      coefficients (fst point)

PowerSeriesUniformlyCauchyOnRadius :
  RealSequence → ℝ → Type
PowerSeriesUniformlyCauchyOnRadius
  coefficients radius =
    UniformlyCauchySeries
      (ClosedAbsRadius radius)
      (powerSeriesTermsOnClosedRadius
        coefficients radius)

PowerSeriesUniformlyAbsolutelyCauchyOnRadius :
  RealSequence → ℝ → Type
PowerSeriesUniformlyAbsolutelyCauchyOnRadius
  coefficients radius =
    UniformlyAbsolutelyCauchySeries
      (ClosedAbsRadius radius)
      (powerSeriesTermsOnClosedRadius
        coefficients radius)

powerSeriesUniformlyAbsolutelyCauchyByCoefficientMajorant :
  ∀ coefficients majorant radius →
  CoefficientMajorizedBy
    coefficients majorant →
  NonnegativeCoefficients majorant →
  IsCauchySeries
    (powerSeriesTerms majorant radius) →
  PowerSeriesUniformlyAbsolutelyCauchyOnRadius
    coefficients radius
powerSeriesUniformlyAbsolutelyCauchyByCoefficientMajorant
  coefficients majorant radius
  coefficients-majorized
  majorant-nonnegative
  majorant-cauchy =
    familyDominatedByCauchySeriesIsUniformlyAbsolutelyCauchy
      (ClosedAbsRadius radius)
      (powerSeriesTermsOnClosedRadius
        coefficients radius)
      (powerSeriesTerms
        majorant radius)
      dominates
      majorant-cauchy
  where
  dominates :
    ∀ point n →
    absℝ
      (powerSeriesTermsOnClosedRadius
        coefficients radius point n)
      ≤ℝ
    powerSeriesTerms majorant radius n
  dominates point n =
    powerSeriesTermAbsBoundByCoefficientMajorant
      coefficients majorant
      (fst point) radius
      coefficients-majorized
      majorant-nonnegative
      (snd point)
      n

powerSeriesUniformlyCauchyByCoefficientMajorant :
  ∀ coefficients majorant radius →
  CoefficientMajorizedBy
    coefficients majorant →
  NonnegativeCoefficients majorant →
  IsCauchySeries
    (powerSeriesTerms majorant radius) →
  PowerSeriesUniformlyCauchyOnRadius
    coefficients radius
powerSeriesUniformlyCauchyByCoefficientMajorant
  coefficients majorant radius
  coefficients-majorized
  majorant-nonnegative
  majorant-cauchy =
    uniformAbsoluteCauchySeriesIsUniformCauchy
      (ClosedAbsRadius radius)
      (powerSeriesTermsOnClosedRadius
        coefficients radius)
      (powerSeriesUniformlyAbsolutelyCauchyByCoefficientMajorant
        coefficients majorant radius
        coefficients-majorized
        majorant-nonnegative
        majorant-cauchy)

formalDerivativePowerSeriesUniformlyAbsolutelyCauchyByCoefficientMajorant :
  ∀ coefficients majorant radius →
  CoefficientMajorizedBy
    coefficients majorant →
  NonnegativeCoefficients majorant →
  IsCauchySeries
    (powerSeriesTerms
      (formalDerivativeMajorant majorant)
      radius) →
  PowerSeriesUniformlyAbsolutelyCauchyOnRadius
    (formalDerivative coefficients)
    radius
formalDerivativePowerSeriesUniformlyAbsolutelyCauchyByCoefficientMajorant
  coefficients majorant radius
  coefficients-majorized
  majorant-nonnegative
  derivative-majorant-cauchy =
    powerSeriesUniformlyAbsolutelyCauchyByCoefficientMajorant
      (formalDerivative coefficients)
      (formalDerivativeMajorant majorant)
      radius
      (formalDerivativePresCoefficientMajorant
        coefficients majorant
        coefficients-majorized)
      (formalDerivativeMajorant-nonnegative
        majorant majorant-nonnegative)
      derivative-majorant-cauchy

formalDerivativePowerSeriesUniformlyCauchyByCoefficientMajorant :
  ∀ coefficients majorant radius →
  CoefficientMajorizedBy
    coefficients majorant →
  NonnegativeCoefficients majorant →
  IsCauchySeries
    (powerSeriesTerms
      (formalDerivativeMajorant majorant)
      radius) →
  PowerSeriesUniformlyCauchyOnRadius
    (formalDerivative coefficients)
    radius
formalDerivativePowerSeriesUniformlyCauchyByCoefficientMajorant
  coefficients majorant radius
  coefficients-majorized
  majorant-nonnegative
  derivative-majorant-cauchy =
    powerSeriesUniformlyCauchyByCoefficientMajorant
      (formalDerivative coefficients)
      (formalDerivativeMajorant majorant)
      radius
      (formalDerivativePresCoefficientMajorant
        coefficients majorant
        coefficients-majorized)
      (formalDerivativeMajorant-nonnegative
        majorant majorant-nonnegative)
      derivative-majorant-cauchy

opaque
  formalDerivativePowerSeriesUniformlyCauchyByCoefficientMajorantWithin :
    ∀ coefficients majorant inner-radius outer-radius →
    CoefficientMajorizedBy
      coefficients majorant →
    NonnegativeCoefficients majorant →
    0 ≤ℝ inner-radius →
    inner-radius ≤ℝ outer-radius →
    IsCauchySeries
      (powerSeriesTerms
        (formalDerivativeMajorant majorant)
        outer-radius) →
    PowerSeriesUniformlyCauchyOnRadius
      (formalDerivative coefficients)
      inner-radius
  formalDerivativePowerSeriesUniformlyCauchyByCoefficientMajorantWithin
    coefficients majorant inner-radius outer-radius
    coefficients-majorized majorant-nonnegative
    inner-nonnegative inner≤outer
    outer-derivative-majorant-cauchy =
      formalDerivativePowerSeriesUniformlyCauchyByCoefficientMajorant
        coefficients majorant inner-radius
        coefficients-majorized majorant-nonnegative
        (nonnegativePowerSeriesIsCauchyWithinRadius
          (formalDerivativeMajorant majorant)
          inner-radius outer-radius
          (formalDerivativeMajorant-nonnegative
            majorant majorant-nonnegative)
          inner-nonnegative inner≤outer
          outer-derivative-majorant-cauchy)

boundedPowerSeriesUniformlyAbsolutelyCauchy :
  ∀ C q coefficients →
  CoefficientAbsBound C coefficients →
  fst q ℚ.< 1 →
  PowerSeriesUniformlyAbsolutelyCauchyOnRadius
    coefficients
    (rat (fst q))
boundedPowerSeriesUniformlyAbsolutelyCauchy
  C q coefficients coefficients-bounded q<1 =
    familyDominatedByCauchySeriesIsUniformlyAbsolutelyCauchy
      (ClosedAbsRadius (rat (fst q)))
      (powerSeriesTermsOnClosedRadius
        coefficients (rat (fst q)))
      (coefficientGeometricMajorant C q)
      dominates
      (coefficientGeometricMajorantIsCauchy
        C q q<1)
  where
  dominates :
    ∀ point n →
    absℝ
      (powerSeriesTermsOnClosedRadius
        coefficients
        (rat (fst q))
        point n)
      ≤ℝ
    coefficientGeometricMajorant C q n
  dominates point n =
    powerSeriesTermAbsBound
      C q coefficients (fst point)
      coefficients-bounded
      (snd point)
      n

boundedPowerSeriesUniformlyCauchy :
  ∀ C q coefficients →
  CoefficientAbsBound C coefficients →
  fst q ℚ.< 1 →
  PowerSeriesUniformlyCauchyOnRadius
    coefficients
    (rat (fst q))
boundedPowerSeriesUniformlyCauchy
  C q coefficients coefficients-bounded q<1 =
    uniformAbsoluteCauchySeriesIsUniformCauchy
      (ClosedAbsRadius (rat (fst q)))
      (powerSeriesTermsOnClosedRadius
        coefficients (rat (fst q)))
      (boundedPowerSeriesUniformlyAbsolutelyCauchy
        C q coefficients
        coefficients-bounded q<1)

powerSeriesUniformlyAbsolutelyCauchyAt :
  ∀ coefficients radius →
  PowerSeriesUniformlyAbsolutelyCauchyOnRadius
    coefficients radius →
  ∀ point →
  IsAbsolutelyCauchySeries
    (powerSeriesTerms
      coefficients (fst point))
powerSeriesUniformlyAbsolutelyCauchyAt
  coefficients radius uniform =
    uniformlyAbsolutelyCauchySeriesAt
      (ClosedAbsRadius radius)
      (powerSeriesTermsOnClosedRadius
        coefficients radius)
      uniform

powerSeriesUniformlyCauchyAt :
  ∀ coefficients radius →
  PowerSeriesUniformlyCauchyOnRadius
    coefficients radius →
  ∀ point →
  IsCauchySeries
    (powerSeriesTerms
      coefficients (fst point))
powerSeriesUniformlyCauchyAt
  coefficients radius uniform =
    uniformlyCauchySeriesAt
      (ClosedAbsRadius radius)
      (powerSeriesTermsOnClosedRadius
        coefficients radius)
      uniform

powerSeriesUniformValueOnClosedRadius :
  ∀ coefficients radius →
  PowerSeriesUniformlyCauchyOnRadius
    coefficients radius →
  ClosedAbsRadius radius →
  ℝ
powerSeriesUniformValueOnClosedRadius
  coefficients radius uniform =
    uniformSeriesValue
      (ClosedAbsRadius radius)
      (powerSeriesTermsOnClosedRadius
        coefficients radius)
      uniform

private
  constantOnClosedRadiusIsContinuous :
    ∀ radius coefficient →
    isContinuous
      (snd
        (ClosedAbsRadiusPremetricSpace
          radius))
      (λ _ → coefficient)
      (snd ℝPremetricSpace)
  constantOnClosedRadiusIsContinuous
    radius coefficient point
    .IsContinuousAt.pres≈ ε =
      return
        ( 1
        , λ _ _ →
            refl∼ coefficient ε
        )

  powerOnClosedRadiusIsContinuous :
    ∀ radius n →
    isContinuous
      (snd
        (ClosedAbsRadiusPremetricSpace
          radius))
      (λ point → fst point ^ⁿ n)
      (snd ℝPremetricSpace)
  powerOnClosedRadiusIsContinuous
    radius n point
    .IsContinuousAt.pres≈ ε = do
      δ , power-near ←
        powIsContinuous n (fst point)
          .IsContinuousAt.pres≈ ε
      return
        ( δ
        , λ other point∼other →
            power-near
              (fst other)
              point∼other
        )

powerSeriesTermOnClosedRadiusIsContinuous :
  ∀ coefficients radius n →
  isContinuous
    (snd
      (ClosedAbsRadiusPremetricSpace
        radius))
    (λ point →
      powerSeriesTermsOnClosedRadius
        coefficients radius point n)
    (snd ℝPremetricSpace)
powerSeriesTermOnClosedRadiusIsContinuous
  coefficients radius n =
    mulOfContinuousIsContinuous
      (snd
        (ClosedAbsRadiusPremetricSpace
          radius))
      (λ _ → coefficients n)
      (λ point → fst point ^ⁿ n)
      (constantOnClosedRadiusIsContinuous
        radius (coefficients n))
      (powerOnClosedRadiusIsContinuous
        radius n)

powerSeriesUniformValueOnClosedRadiusIsContinuous :
  ∀ coefficients radius →
  (uniform :
    PowerSeriesUniformlyCauchyOnRadius
      coefficients radius) →
  isContinuous
    (snd
      (ClosedAbsRadiusPremetricSpace
        radius))
    (powerSeriesUniformValueOnClosedRadius
      coefficients radius uniform)
    (snd ℝPremetricSpace)
powerSeriesUniformValueOnClosedRadiusIsContinuous
  coefficients radius uniform =
    uniformSeriesValueIsContinuous
      (snd
        (ClosedAbsRadiusPremetricSpace
          radius))
      (powerSeriesTermsOnClosedRadius
        coefficients radius)
      uniform
      (powerSeriesTermOnClosedRadiusIsContinuous
        coefficients radius)
