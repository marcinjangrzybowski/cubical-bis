module Cubical.Analysis.Real.Series.PowerSeries.Difference.Uniform where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Domain.Radius
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Absolute
open import Cubical.Analysis.Real.Series.Uniform
open import Cubical.Analysis.Real.Series.PowerSeries.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Majorant
open import Cubical.Analysis.Real.Series.PowerSeries.Derivative
open import Cubical.Analysis.Real.Series.PowerSeries.Difference


ClosedAbsRadiusPair : ℝ → Type₀
ClosedAbsRadiusPair radius =
  ClosedAbsRadius radius × ClosedAbsRadius radius


ClosedAbsRadiusPairPremetricSpace :
  ℝ → PremetricSpace ℓ-zero ℓ-zero
ClosedAbsRadiusPairPremetricSpace radius =
  PremetricProduct
    (ClosedAbsRadiusPremetricSpace radius)
    (ClosedAbsRadiusPremetricSpace radius)


closedAbsRadiusPairLeft :
  ∀ radius → ClosedAbsRadiusPair radius → ℝ
closedAbsRadiusPairLeft radius point =
  fst (fst point)


closedAbsRadiusPairRight :
  ∀ radius → ClosedAbsRadiusPair radius → ℝ
closedAbsRadiusPairRight radius point =
  fst (snd point)


closedAbsRadiusPairLeftIsContinuous :
  ∀ radius →
  isContinuous
    (ClosedAbsRadiusPairPremetricSpace radius .snd)
    (closedAbsRadiusPairLeft radius)
    (ℝPremetricSpace .snd)
closedAbsRadiusPairLeftIsContinuous
  radius point .IsContinuousAt.pres≈ ε =
  ∣ ε
  , (λ _ point≈other → fst point≈other)
  ∣₁


closedAbsRadiusPairRightIsContinuous :
  ∀ radius →
  isContinuous
    (ClosedAbsRadiusPairPremetricSpace radius .snd)
    (closedAbsRadiusPairRight radius)
    (ℝPremetricSpace .snd)
closedAbsRadiusPairRightIsContinuous
  radius point .IsContinuousAt.pres≈ ε =
  ∣ ε
  , (λ _ point≈other → snd point≈other)
  ∣₁


powerSeriesDifferenceFactorOnClosedRadius :
  RealSequence → ∀ radius →
  ClosedAbsRadiusPair radius → RealSequence
powerSeriesDifferenceFactorOnClosedRadius
  coefficients radius point =
  powerSeriesDifferenceFactor
    coefficients
    (closedAbsRadiusPairLeft radius point)
    (closedAbsRadiusPairRight radius point)


PowerSeriesDifferenceFactorUniformlyCauchyOnRadius :
  RealSequence → ℝ → Type₀
PowerSeriesDifferenceFactorUniformlyCauchyOnRadius
  coefficients radius =
  UniformlyCauchySeries
    (ClosedAbsRadiusPair radius)
    (powerSeriesDifferenceFactorOnClosedRadius
      coefficients radius)


powerSeriesDifferenceFactorUniformlyCauchyOnSmallerRadius :
  ∀ coefficients radius larger →
  radius ≤ℝ larger →
  PowerSeriesDifferenceFactorUniformlyCauchyOnRadius
    coefficients larger →
  PowerSeriesDifferenceFactorUniformlyCauchyOnRadius
    coefficients radius
powerSeriesDifferenceFactorUniformlyCauchyOnSmallerRadius
    coefficients radius larger radius≤larger uniform =
  uniformlyCauchySeriesPrecompose
    (powerSeriesDifferenceFactorOnClosedRadius coefficients larger)
    (λ point →
      fst (closedAbsRadiusMonotoneNE radius larger radius≤larger)
        (fst point)
      , fst (closedAbsRadiusMonotoneNE radius larger radius≤larger)
          (snd point))
    uniform


powerSeriesDifferenceFactorTermOnClosedRadiusIsContinuous :
  ∀ coefficients radius n →
  isContinuous
    (ClosedAbsRadiusPairPremetricSpace radius .snd)
    (λ point →
      powerSeriesDifferenceFactorOnClosedRadius
        coefficients radius point n)
    (ℝPremetricSpace .snd)
powerSeriesDifferenceFactorTermOnClosedRadiusIsContinuous
  coefficients radius n =
  powerSeriesDifferenceFactorOfContinuousIsContinuous
    (ClosedAbsRadiusPairPremetricSpace radius .snd)
    coefficients
    (closedAbsRadiusPairLeft radius)
    (closedAbsRadiusPairRight radius)
    (closedAbsRadiusPairLeftIsContinuous radius)
    (closedAbsRadiusPairRightIsContinuous radius)
    n


powerSeriesDifferenceFactorUniformlyCauchyByDerivativeMajorant :
  ∀ coefficients majorant radius →
  CoefficientMajorizedBy coefficients majorant →
  IsCauchySeries
    (powerSeriesTerms
      (formalDerivativeMajorant majorant) radius) →
  PowerSeriesDifferenceFactorUniformlyCauchyOnRadius
    coefficients radius
powerSeriesDifferenceFactorUniformlyCauchyByDerivativeMajorant
  coefficients majorant radius
  majorized derivative-majorant-cauchy =
  uniformlyDominatedSeriesIsUniformlyCauchy
    (powerSeriesDifferenceFactorOnClosedRadius
      coefficients radius)
    (powerSeriesTerms
      (formalDerivativeMajorant majorant) radius)
    dominates
    derivative-majorant-cauchy
  where
  dominates : ∀ point n →
    absℝ
      (powerSeriesDifferenceFactorOnClosedRadius
        coefficients radius point n)
      ≤ℝ
    powerSeriesTerms
      (formalDerivativeMajorant majorant) radius n
  dominates point n =
    powerSeriesDifferenceFactorTermBoundByDerivativeMajorant
      coefficients majorant
      (closedAbsRadiusPairLeft radius point)
      (closedAbsRadiusPairRight radius point)
      radius majorized
      radius-nonnegative
      (snd (fst point))
      (snd (snd point))
      n
    where
    radius-nonnegative : 0ℝ ≤ℝ radius
    radius-nonnegative =
      ≤ℝ-trans
        0ℝ
        (absℝ (closedAbsRadiusPairLeft radius point))
        radius
        (absNonnegative
          (closedAbsRadiusPairLeft radius point))
        (snd (fst point))


powerSeriesDifferenceFactorUniformlyCauchyByDerivativeMajorantWithin :
  ∀ coefficients majorant inner-radius outer-radius →
  CoefficientMajorizedBy coefficients majorant →
  0ℝ ≤ℝ inner-radius →
  inner-radius ≤ℝ outer-radius →
  IsCauchySeries
    (powerSeriesTerms
      (formalDerivativeMajorant majorant) outer-radius) →
  PowerSeriesDifferenceFactorUniformlyCauchyOnRadius
    coefficients inner-radius
powerSeriesDifferenceFactorUniformlyCauchyByDerivativeMajorantWithin
  coefficients majorant inner-radius outer-radius
  majorized inner-nonnegative inner≤outer
  outer-derivative-majorant-cauchy =
  powerSeriesDifferenceFactorUniformlyCauchyByDerivativeMajorant
    coefficients majorant inner-radius majorized
    inner-derivative-majorant-cauchy
  where
  derivative-majorant-nonnegative :
    NonnegativeCoefficients
      (formalDerivativeMajorant majorant)
  derivative-majorant-nonnegative =
    formalDerivativeMajorant-nonnegative
      majorant
      (coefficientMajorantIsNonnegative
        coefficients majorant majorized)

  abs-inner≤outer : absℝ inner-radius ≤ℝ outer-radius
  abs-inner≤outer =
    subst
      (_≤ℝ outer-radius)
      (sym
        (absOfNonnegative
          inner-radius inner-nonnegative))
      inner≤outer

  inner-derivative-majorant-cauchy :
    IsCauchySeries
      (powerSeriesTerms
        (formalDerivativeMajorant majorant) inner-radius)
  inner-derivative-majorant-cauchy =
    dominatedCauchySeriesIsCauchy
      (powerSeriesTerms
        (formalDerivativeMajorant majorant) inner-radius)
      (powerSeriesTerms
        (formalDerivativeMajorant majorant) outer-radius)
      (powerSeriesTermAbsBoundByCoefficientMajorant
        (formalDerivativeMajorant majorant)
        (formalDerivativeMajorant majorant)
        inner-radius outer-radius
        (nonnegativeCoefficientsSelfMajorized
          (formalDerivativeMajorant majorant)
          derivative-majorant-nonnegative)
        abs-inner≤outer)
      outer-derivative-majorant-cauchy
