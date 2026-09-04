module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.Algebra.CommRing
import Cubical.Algebra.Ring.Properties as RingProperties

open import Cubical.Relation.Premetric.Mappings using (isContinuous)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using
  (1ℝ; mulIdL)
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Operations
open import Cubical.Analysis.Real.Series.PowerSeries.AtZero
open import Cubical.Analysis.Real.Series.PowerSeries.Derivative
open import Cubical.Analysis.Real.Series.PowerSeries.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Coefficients
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Convergence
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Parity
open import Cubical.Analysis.Real.Calculus.Derivative.Base
open import Cubical.Analysis.Real.Calculus.Derivative.Continuity


private
  module ℝRing =
    RingProperties.RingTheory (CommRing→Ring ℝCommRing)


sinℝ : ℝ → ℝ
sinℝ =
  entirePowerSeriesValue
    sineCoefficients sinePowerSeriesEntireUniformlyCauchy


cosℝ : ℝ → ℝ
cosℝ =
  entirePowerSeriesValue
    cosineCoefficients cosinePowerSeriesEntireUniformlyCauchy


sinePowerSeriesHasSum : ∀ x →
  HasSum (powerSeriesTerms sineCoefficients x) (sinℝ x)
sinePowerSeriesHasSum x =
  seriesSumHasSum
    (powerSeriesTerms sineCoefficients x)
    (entirePowerSeriesSummableAt
      sineCoefficients sinePowerSeriesEntireUniformlyCauchy x)


cosinePowerSeriesHasSum : ∀ x →
  HasSum (powerSeriesTerms cosineCoefficients x) (cosℝ x)
cosinePowerSeriesHasSum x =
  seriesSumHasSum
    (powerSeriesTerms cosineCoefficients x)
    (entirePowerSeriesSummableAt
      cosineCoefficients cosinePowerSeriesEntireUniformlyCauchy x)


sinℝ-zero : sinℝ 0ℝ ≡ 0ℝ
sinℝ-zero =
  powerSeriesValueAtZero
    sineCoefficients
    (entirePowerSeriesSummableAt
      sineCoefficients sinePowerSeriesEntireUniformlyCauchy 0ℝ)
  ∙ sineCoefficients-zero


cosℝ-zero : cosℝ 0ℝ ≡ 1ℝ
cosℝ-zero =
  powerSeriesValueAtZero
    cosineCoefficients
    (entirePowerSeriesSummableAt
      cosineCoefficients cosinePowerSeriesEntireUniformlyCauchy 0ℝ)
  ∙ cosineCoefficients-zero


negativeOneMul : ∀ x → (- 1ℝ) · x ≡ - x
negativeOneMul x =
  ℝRing.-DistL· 1ℝ x
  ∙ cong -_ (mulIdL x)


opaque
  sinℝ-neg : ∀ x → sinℝ (- x) ≡ - sinℝ x
  sinℝ-neg x =
    seriesSumPresPath
      (powerSeriesTerms sineCoefficients (- x))
      (λ n → - powerSeriesTerms sineCoefficients x n)
      (cong
        (powerSeriesTerms sineCoefficients)
        (sym (negativeOneMul x))
        ∙ sinePowerSeriesTerms-negOne x)
      (entirePowerSeriesSummableAt
        sineCoefficients sinePowerSeriesEntireUniformlyCauchy (- x))
      (negSummable
        (powerSeriesTerms sineCoefficients x)
        (entirePowerSeriesSummableAt
          sineCoefficients sinePowerSeriesEntireUniformlyCauchy x))
    ∙ seriesSum-neg
        (powerSeriesTerms sineCoefficients x)
        (entirePowerSeriesSummableAt
          sineCoefficients sinePowerSeriesEntireUniformlyCauchy x)
        (negSummable
          (powerSeriesTerms sineCoefficients x)
          (entirePowerSeriesSummableAt
            sineCoefficients sinePowerSeriesEntireUniformlyCauchy x))


  cosℝ-neg : ∀ x → cosℝ (- x) ≡ cosℝ x
  cosℝ-neg x =
    seriesSumPresPath
      (powerSeriesTerms cosineCoefficients (- x))
      (powerSeriesTerms cosineCoefficients x)
      (cong
        (powerSeriesTerms cosineCoefficients)
        (sym (negativeOneMul x))
        ∙ cosinePowerSeriesTerms-negOne x)
      (entirePowerSeriesSummableAt
        cosineCoefficients cosinePowerSeriesEntireUniformlyCauchy (- x))
      (entirePowerSeriesSummableAt
        cosineCoefficients cosinePowerSeriesEntireUniformlyCauchy x)


sineLocalDerivativeValue : ℝ → ℝ
sineLocalDerivativeValue x =
  entireFormalDerivativeValueAtRadius
    sineCoefficients
    sineFormalDerivativePowerSeriesEntireUniformlyCauchy
    (entireRadiusAt x) x (entireRadiusAt-interior x)


cosineLocalDerivativeValue : ℝ → ℝ
cosineLocalDerivativeValue x =
  entireFormalDerivativeValueAtRadius
    cosineCoefficients
    cosineFormalDerivativePowerSeriesEntireUniformlyCauchy
    (entireRadiusAt x) x (entireRadiusAt-interior x)


cosℝ-agreesWithSineFormalDerivative : ∀ x →
  cosℝ x ≡
  entirePowerSeriesValue
    (formalDerivative sineCoefficients)
    sineFormalDerivativePowerSeriesEntireUniformlyCauchy x
cosℝ-agreesWithSineFormalDerivative x =
  seriesSumPresPath
    (powerSeriesTerms cosineCoefficients x)
    (powerSeriesTerms (formalDerivative sineCoefficients) x)
    (cong
      (λ coefficients → powerSeriesTerms coefficients x)
      (sym formalDerivative-sineCoefficients))
    (entirePowerSeriesSummableAt
      cosineCoefficients cosinePowerSeriesEntireUniformlyCauchy x)
    (entirePowerSeriesSummableAt
      (formalDerivative sineCoefficients)
      sineFormalDerivativePowerSeriesEntireUniformlyCauchy x)


cosℝ-agreesWithSineLocalDerivative : ∀ x →
  cosℝ x ≡ sineLocalDerivativeValue x
cosℝ-agreesWithSineLocalDerivative x =
  cosℝ-agreesWithSineFormalDerivative x
  ∙ fst
      (entirePowerSeriesValueFormalDerivativeAtCanonicalRadius
        sineCoefficients
        sinePowerSeriesEntireUniformlyCauchy
        sineFormalDerivativePowerSeriesEntireUniformlyCauchy
        sinePowerSeriesDifferenceFactorEntireUniformlyCauchy x)


cosineFormalDerivative-agreesWithNegativeSine : ∀ x →
  entirePowerSeriesValue
    (formalDerivative cosineCoefficients)
    cosineFormalDerivativePowerSeriesEntireUniformlyCauchy x
  ≡ - sinℝ x
cosineFormalDerivative-agreesWithNegativeSine x =
  seriesSumPresPath
    (powerSeriesTerms (formalDerivative cosineCoefficients) x)
    (powerSeriesTerms (λ n → - sineCoefficients n) x)
    (cong
      (λ coefficients → powerSeriesTerms coefficients x)
      formalDerivative-cosineCoefficients)
    (entirePowerSeriesSummableAt
      (formalDerivative cosineCoefficients)
      cosineFormalDerivativePowerSeriesEntireUniformlyCauchy x)
    negative-sine-summable
  ∙ powerSeriesValue-neg
      sineCoefficients x sine-summable negative-sine-summable
  where
  sine-summable : PowerSeriesSummableAt sineCoefficients x
  sine-summable =
    entirePowerSeriesSummableAt
      sineCoefficients sinePowerSeriesEntireUniformlyCauchy x

  negative-sine-summable :
    PowerSeriesSummableAt (λ n → - sineCoefficients n) x
  negative-sine-summable =
    powerSeriesNegSummable sineCoefficients x sine-summable


negativeSinℝ-agreesWithCosineLocalDerivative : ∀ x →
  - sinℝ x ≡ cosineLocalDerivativeValue x
negativeSinℝ-agreesWithCosineLocalDerivative x =
  sym (cosineFormalDerivative-agreesWithNegativeSine x)
  ∙ fst
      (entirePowerSeriesValueFormalDerivativeAtCanonicalRadius
        cosineCoefficients
        cosinePowerSeriesEntireUniformlyCauchy
        cosineFormalDerivativePowerSeriesEntireUniformlyCauchy
        cosinePowerSeriesDifferenceFactorEntireUniformlyCauchy x)


sinℝHasCosineLocalDerivative : ∀ x →
  (cosℝ x ≡ sineLocalDerivativeValue x)
  × IsDerivativeAt sinℝ (sineLocalDerivativeValue x) x
sinℝHasCosineLocalDerivative x =
  cosℝ-agreesWithSineLocalDerivative x
  , snd
      (entirePowerSeriesValueFormalDerivativeAtCanonicalRadius
        sineCoefficients
        sinePowerSeriesEntireUniformlyCauchy
        sineFormalDerivativePowerSeriesEntireUniformlyCauchy
        sinePowerSeriesDifferenceFactorEntireUniformlyCauchy x)


cosℝHasNegativeSineLocalDerivative : ∀ x →
  (- sinℝ x ≡ cosineLocalDerivativeValue x)
  × IsDerivativeAt cosℝ (cosineLocalDerivativeValue x) x
cosℝHasNegativeSineLocalDerivative x =
  negativeSinℝ-agreesWithCosineLocalDerivative x
  , snd
      (entirePowerSeriesValueFormalDerivativeAtCanonicalRadius
        cosineCoefficients
        cosinePowerSeriesEntireUniformlyCauchy
        cosineFormalDerivativePowerSeriesEntireUniformlyCauchy
        cosinePowerSeriesDifferenceFactorEntireUniformlyCauchy x)


sinℝHasDerivative : IsDerivative sinℝ cosℝ
sinℝHasDerivative x =
  subst
    (λ derivative-value →
      IsDerivativeAt sinℝ derivative-value x)
    (sym (cosℝ-agreesWithSineLocalDerivative x))
    (snd (sinℝHasCosineLocalDerivative x))


cosℝHasDerivative : IsDerivative cosℝ (λ x → - sinℝ x)
cosℝHasDerivative x =
  subst
    (λ derivative-value →
      IsDerivativeAt cosℝ derivative-value x)
    (sym (negativeSinℝ-agreesWithCosineLocalDerivative x))
    (snd (cosℝHasNegativeSineLocalDerivative x))


sinℝHasDerivativeCosℝ : IsDerivative sinℝ cosℝ
sinℝHasDerivativeCosℝ = sinℝHasDerivative


cosℝHasDerivativeNegativeSinℝ :
  IsDerivative cosℝ (λ x → - sinℝ x)
cosℝHasDerivativeNegativeSinℝ = cosℝHasDerivative


sinℝIsContinuous :
  isContinuous
    (ℝPremetricSpace .snd) sinℝ (ℝPremetricSpace .snd)
sinℝIsContinuous =
  derivativeIsContinuous sinℝ cosℝ sinℝHasDerivative


cosℝIsContinuous :
  isContinuous
    (ℝPremetricSpace .snd) cosℝ (ℝPremetricSpace .snd)
cosℝIsContinuous =
  derivativeIsContinuous cosℝ (λ x → - sinℝ x) cosℝHasDerivative
