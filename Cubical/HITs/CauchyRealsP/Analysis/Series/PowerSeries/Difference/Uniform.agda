module Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Difference.Uniform where

open import Cubical.Foundations.Prelude

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
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Derivative
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Difference
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Uniform

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product

ClosedAbsRadiusPair :
  ℝ → Type
ClosedAbsRadiusPair radius =
  ClosedAbsRadius radius
    × ClosedAbsRadius radius

ClosedAbsRadiusPairPremetricSpace :
  ℝ → PremetricSpace ℓ-zero ℓ-zero
ClosedAbsRadiusPairPremetricSpace radius =
  PremetricProduct
    (ClosedAbsRadiusPremetricSpace radius)
    (ClosedAbsRadiusPremetricSpace radius)

closedAbsRadiusPairLeft :
  ∀ radius →
  ClosedAbsRadiusPair radius → ℝ
closedAbsRadiusPairLeft radius point =
  fst (fst point)

closedAbsRadiusPairRight :
  ∀ radius →
  ClosedAbsRadiusPair radius → ℝ
closedAbsRadiusPairRight radius point =
  fst (snd point)

closedAbsRadiusPairLeftIsContinuous :
  ∀ radius →
  isContinuous
    (snd
      (ClosedAbsRadiusPairPremetricSpace
        radius))
    (closedAbsRadiusPairLeft radius)
    (snd ℝPremetricSpace)
closedAbsRadiusPairLeftIsContinuous
  radius point .IsContinuousAt.pres≈ ε =
    return
      ( ε
      , λ _ point∼other →
          fst point∼other
      )

closedAbsRadiusPairRightIsContinuous :
  ∀ radius →
  isContinuous
    (snd
      (ClosedAbsRadiusPairPremetricSpace
        radius))
    (closedAbsRadiusPairRight radius)
    (snd ℝPremetricSpace)
closedAbsRadiusPairRightIsContinuous
  radius point .IsContinuousAt.pres≈ ε =
    return
      ( ε
      , λ _ point∼other →
          snd point∼other
      )

powerSeriesDifferenceFactorOnClosedRadius :
  RealSequence →
  ∀ radius →
  ClosedAbsRadiusPair radius →
  RealSequence
powerSeriesDifferenceFactorOnClosedRadius
  coefficients radius point =
    powerSeriesDifferenceFactor
      coefficients
      (closedAbsRadiusPairLeft radius point)
      (closedAbsRadiusPairRight radius point)

PowerSeriesDifferenceFactorUniformlyCauchyOnRadius :
  RealSequence → ℝ → Type
PowerSeriesDifferenceFactorUniformlyCauchyOnRadius
  coefficients radius =
    UniformlyCauchySeries
      (ClosedAbsRadiusPair radius)
      (powerSeriesDifferenceFactorOnClosedRadius
        coefficients radius)

PowerSeriesDifferenceFactorUniformlyAbsolutelyCauchyOnRadius :
  RealSequence → ℝ → Type
PowerSeriesDifferenceFactorUniformlyAbsolutelyCauchyOnRadius
  coefficients radius =
    UniformlyAbsolutelyCauchySeries
      (ClosedAbsRadiusPair radius)
      (powerSeriesDifferenceFactorOnClosedRadius
        coefficients radius)

powerSeriesDifferenceFactorUniformlyAbsolutelyCauchyByDerivativeMajorant :
  ∀ coefficients majorant radius →
  CoefficientMajorizedBy
    coefficients majorant →
  NonnegativeCoefficients majorant →
  IsCauchySeries
    (powerSeriesTerms
      (formalDerivativeMajorant majorant)
      radius) →
  PowerSeriesDifferenceFactorUniformlyAbsolutelyCauchyOnRadius
    coefficients radius
powerSeriesDifferenceFactorUniformlyAbsolutelyCauchyByDerivativeMajorant
  coefficients majorant radius
  majorized nonnegative derivative-majorant-cauchy =
    familyDominatedByCauchySeriesIsUniformlyAbsolutelyCauchy
      (ClosedAbsRadiusPair radius)
      (powerSeriesDifferenceFactorOnClosedRadius
        coefficients radius)
      (powerSeriesTerms
        (formalDerivativeMajorant majorant)
        radius)
      dominates
      derivative-majorant-cauchy
  where
  dominates :
    ∀ point n →
    absℝ
      (powerSeriesDifferenceFactorOnClosedRadius
        coefficients radius point n)
      ≤ℝ
    powerSeriesTerms
      (formalDerivativeMajorant majorant)
      radius n
  dominates point n =
    powerSeriesDifferenceFactorTermBoundByDerivativeMajorant
      coefficients majorant
      (closedAbsRadiusPairLeft radius point)
      (closedAbsRadiusPairRight radius point)
      radius
      majorized nonnegative
      radius-nonnegative
        (snd (fst point))
        (snd (snd point))
        n
    where
    radius-nonnegative :
      0 ≤ℝ radius
    radius-nonnegative =
      ≤ℝ-trans
        0
        (absℝ
          (closedAbsRadiusPairLeft
            radius point))
        radius
        (absNonnegative
          (closedAbsRadiusPairLeft
            radius point))
        (snd (fst point))

powerSeriesDifferenceFactorUniformlyAbsolutelyCauchyByDerivativeMajorantWithin :
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
  PowerSeriesDifferenceFactorUniformlyAbsolutelyCauchyOnRadius
    coefficients inner-radius
powerSeriesDifferenceFactorUniformlyAbsolutelyCauchyByDerivativeMajorantWithin
  coefficients majorant inner-radius outer-radius
  majorized nonnegative inner-nonnegative
  inner≤outer outer-derivative-majorant-cauchy =
    powerSeriesDifferenceFactorUniformlyAbsolutelyCauchyByDerivativeMajorant
      coefficients majorant inner-radius
      majorized nonnegative
      (nonnegativePowerSeriesIsCauchyWithinRadius
        (formalDerivativeMajorant majorant)
        inner-radius outer-radius
        (formalDerivativeMajorant-nonnegative
          majorant nonnegative)
        inner-nonnegative inner≤outer
        outer-derivative-majorant-cauchy)

powerSeriesDifferenceFactorUniformlyCauchyByDerivativeMajorant :
  ∀ coefficients majorant radius →
  CoefficientMajorizedBy
    coefficients majorant →
  NonnegativeCoefficients majorant →
  IsCauchySeries
    (powerSeriesTerms
      (formalDerivativeMajorant majorant)
      radius) →
  PowerSeriesDifferenceFactorUniformlyCauchyOnRadius
    coefficients radius
powerSeriesDifferenceFactorUniformlyCauchyByDerivativeMajorant
  coefficients majorant radius
  majorized nonnegative derivative-majorant-cauchy =
    uniformAbsoluteCauchySeriesIsUniformCauchy
      (ClosedAbsRadiusPair radius)
      (powerSeriesDifferenceFactorOnClosedRadius
        coefficients radius)
      (powerSeriesDifferenceFactorUniformlyAbsolutelyCauchyByDerivativeMajorant
        coefficients majorant radius
        majorized nonnegative
        derivative-majorant-cauchy)

powerSeriesDifferenceFactorUniformlyCauchyByDerivativeMajorantWithin :
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
  PowerSeriesDifferenceFactorUniformlyCauchyOnRadius
    coefficients inner-radius
powerSeriesDifferenceFactorUniformlyCauchyByDerivativeMajorantWithin
  coefficients majorant inner-radius outer-radius
  majorized nonnegative inner-nonnegative
  inner≤outer outer-derivative-majorant-cauchy =
    uniformAbsoluteCauchySeriesIsUniformCauchy
      (ClosedAbsRadiusPair inner-radius)
      (powerSeriesDifferenceFactorOnClosedRadius
        coefficients inner-radius)
      (powerSeriesDifferenceFactorUniformlyAbsolutelyCauchyByDerivativeMajorantWithin
        coefficients majorant inner-radius outer-radius
        majorized nonnegative inner-nonnegative
        inner≤outer outer-derivative-majorant-cauchy)

powerSeriesDifferenceFactorUniformlyCauchyByDerivativeMajorantWithinStrict :
  ∀ coefficients majorant inner-radius outer-radius →
  CoefficientMajorizedBy
    coefficients majorant →
  NonnegativeCoefficients majorant →
  0 ≤ℝ inner-radius →
  inner-radius <ℝ outer-radius →
  IsCauchySeries
    (powerSeriesTerms
      (formalDerivativeMajorant majorant)
      outer-radius) →
  PowerSeriesDifferenceFactorUniformlyCauchyOnRadius
    coefficients inner-radius
powerSeriesDifferenceFactorUniformlyCauchyByDerivativeMajorantWithinStrict
  coefficients majorant inner-radius outer-radius
  majorized nonnegative inner-nonnegative inner<outer =
    powerSeriesDifferenceFactorUniformlyCauchyByDerivativeMajorantWithin
      coefficients majorant inner-radius outer-radius
      majorized nonnegative inner-nonnegative
      (<ℝ-weaken
        inner-radius outer-radius inner<outer)

powerSeriesDifferenceFactorTermOnClosedRadiusIsContinuous :
  ∀ coefficients radius n →
  isContinuous
    (snd
      (ClosedAbsRadiusPairPremetricSpace
        radius))
    (λ point →
      powerSeriesDifferenceFactorOnClosedRadius
        coefficients radius point n)
    (snd ℝPremetricSpace)
powerSeriesDifferenceFactorTermOnClosedRadiusIsContinuous
  coefficients radius n =
    powerSeriesDifferenceFactorOfContinuousIsContinuous
      (snd
        (ClosedAbsRadiusPairPremetricSpace
          radius))
      coefficients
      (closedAbsRadiusPairLeft radius)
      (closedAbsRadiusPairRight radius)
      (closedAbsRadiusPairLeftIsContinuous
        radius)
      (closedAbsRadiusPairRightIsContinuous
        radius)
      n

powerSeriesDifferenceFactorValueOnClosedRadius :
  ∀ coefficients radius →
  PowerSeriesDifferenceFactorUniformlyCauchyOnRadius
    coefficients radius →
  ClosedAbsRadiusPair radius →
  ℝ
powerSeriesDifferenceFactorValueOnClosedRadius
  coefficients radius uniform =
    uniformSeriesValue
      (ClosedAbsRadiusPair radius)
      (powerSeriesDifferenceFactorOnClosedRadius
        coefficients radius)
      uniform

powerSeriesDifferenceFactorValueOnClosedRadiusIsContinuous :
  ∀ coefficients radius →
  (uniform :
    PowerSeriesDifferenceFactorUniformlyCauchyOnRadius
      coefficients radius) →
  isContinuous
    (snd
      (ClosedAbsRadiusPairPremetricSpace
        radius))
    (powerSeriesDifferenceFactorValueOnClosedRadius
      coefficients radius uniform)
    (snd ℝPremetricSpace)
powerSeriesDifferenceFactorValueOnClosedRadiusIsContinuous
  coefficients radius uniform =
    uniformSeriesValueIsContinuous
      (snd
        (ClosedAbsRadiusPairPremetricSpace
          radius))
      (powerSeriesDifferenceFactorOnClosedRadius
        coefficients radius)
      uniform
      (powerSeriesDifferenceFactorTermOnClosedRadiusIsContinuous
        coefficients radius)
