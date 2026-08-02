module Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Majorant where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Sequence
open import Cubical.HITs.CauchyRealsP.Analysis.Series.Base
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Absolute
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Convolution.Mertens
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Base

CoefficientMajorizedBy :
  RealSequence → RealSequence → Type
CoefficientMajorizedBy coefficients majorant =
  ∀ n →
  absℝ (coefficients n)
    ≤ℝ majorant n

NonnegativeCoefficients :
  RealSequence → Type
NonnegativeCoefficients coefficients =
  ∀ n → 0 ≤ℝ coefficients n

nonnegativeCoefficientsSelfMajorized :
  ∀ coefficients →
  NonnegativeCoefficients coefficients →
  CoefficientMajorizedBy
    coefficients coefficients
nonnegativeCoefficientsSelfMajorized
  coefficients nonnegative n =
    subst
      (_≤ℝ coefficients n)
      (sym
        (absOfNonnegative
          (coefficients n)
          (nonnegative n)))
      (≤ℝ-refl (coefficients n))

powerSeriesTermAbsBoundByCoefficientMajorant :
  ∀ coefficients majorant x radius →
  CoefficientMajorizedBy
    coefficients majorant →
  NonnegativeCoefficients majorant →
  absℝ x ≤ℝ radius →
  ∀ n →
  absℝ
    (powerSeriesTerms coefficients x n)
    ≤ℝ
  powerSeriesTerms majorant radius n
powerSeriesTermAbsBoundByCoefficientMajorant
  coefficients majorant x radius
  coefficients-majorized
  majorant-nonnegative
  absx≤radius n =
    subst
      (_≤ℝ
        powerSeriesTerms majorant radius n)
      (sym absolute-term-path)
      product-bound
  where
  absolute-term-path :
    absℝ
      (powerSeriesTerms coefficients x n)
      ≡
    absℝ (coefficients n)
      · absℝ x ^ⁿ n
  absolute-term-path =
    absMul
      (coefficients n)
      (x ^ⁿ n)
    ∙ cong
        (absℝ (coefficients n) ·_)
        (absPow n x)

  radius-power-bound :
    absℝ x ^ⁿ n
      ≤ℝ radius ^ⁿ n
  radius-power-bound =
    powMonoℝ n
      (absNonnegative x)
      absx≤radius

  product-bound :
    absℝ (coefficients n)
      · absℝ x ^ⁿ n
      ≤ℝ
    powerSeriesTerms majorant radius n
  product-bound =
    mulMono≤
      (absℝ (coefficients n))
      (majorant n)
      (absℝ x ^ⁿ n)
      (radius ^ⁿ n)
      (majorant-nonnegative n)
      (powNonnegativeℝ
        (absℝ x) n
        (absNonnegative x))
      (coefficients-majorized n)
      radius-power-bound

powerSeriesIsAbsolutelyCauchyByCoefficientMajorant :
  ∀ coefficients majorant x radius →
  CoefficientMajorizedBy
    coefficients majorant →
  NonnegativeCoefficients majorant →
  absℝ x ≤ℝ radius →
  IsCauchySeries
    (powerSeriesTerms majorant radius) →
  IsAbsolutelyCauchySeries
    (powerSeriesTerms coefficients x)
powerSeriesIsAbsolutelyCauchyByCoefficientMajorant
  coefficients majorant x radius
  coefficients-majorized
  majorant-nonnegative
  absx≤radius
  majorant-cauchy =
    dominatedCauchySeriesIsCauchy
      (absℝ ∘
        powerSeriesTerms coefficients x)
      (powerSeriesTerms majorant radius)
      dominates
      majorant-cauchy
  where
  dominates : ∀ n →
    absℝ
      (absℝ
        (powerSeriesTerms coefficients x n))
      ≤ℝ
    powerSeriesTerms majorant radius n
  dominates n =
    subst
      (_≤ℝ
        powerSeriesTerms majorant radius n)
      (sym
        (absIdem
          (powerSeriesTerms coefficients x n)))
      (powerSeriesTermAbsBoundByCoefficientMajorant
        coefficients majorant x radius
        coefficients-majorized
        majorant-nonnegative
        absx≤radius n)

powerSeriesIsCauchyByCoefficientMajorant :
  ∀ coefficients majorant x radius →
  CoefficientMajorizedBy
    coefficients majorant →
  NonnegativeCoefficients majorant →
  absℝ x ≤ℝ radius →
  IsCauchySeries
    (powerSeriesTerms majorant radius) →
  IsCauchySeries
    (powerSeriesTerms coefficients x)
powerSeriesIsCauchyByCoefficientMajorant
  coefficients majorant x radius
  coefficients-majorized
  majorant-nonnegative
  absx≤radius
  majorant-cauchy =
    absoluteCauchySeriesIsCauchy
      (powerSeriesTerms coefficients x)
      (powerSeriesIsAbsolutelyCauchyByCoefficientMajorant
        coefficients majorant x radius
        coefficients-majorized
        majorant-nonnegative
        absx≤radius
        majorant-cauchy)

powerSeriesIsSummableByCoefficientMajorant :
  ∀ coefficients majorant x radius →
  CoefficientMajorizedBy
    coefficients majorant →
  NonnegativeCoefficients majorant →
  absℝ x ≤ℝ radius →
  IsCauchySeries
    (powerSeriesTerms majorant radius) →
  PowerSeriesSummableAt coefficients x
powerSeriesIsSummableByCoefficientMajorant
  coefficients majorant x radius
  coefficients-majorized
  majorant-nonnegative
  absx≤radius
  majorant-cauchy =
    absoluteCauchySeriesIsSummable
      (powerSeriesTerms coefficients x)
      (powerSeriesIsAbsolutelyCauchyByCoefficientMajorant
        coefficients majorant x radius
        coefficients-majorized
        majorant-nonnegative
        absx≤radius
        majorant-cauchy)

nonnegativePowerSeriesIsAbsolutelyCauchyWithinRadius :
  ∀ coefficients inner-radius outer-radius →
  NonnegativeCoefficients coefficients →
  0 ≤ℝ inner-radius →
  inner-radius ≤ℝ outer-radius →
  IsCauchySeries
    (powerSeriesTerms coefficients outer-radius) →
  IsAbsolutelyCauchySeries
    (powerSeriesTerms coefficients inner-radius)
nonnegativePowerSeriesIsAbsolutelyCauchyWithinRadius
  coefficients inner-radius outer-radius
  nonnegative inner-nonnegative inner≤outer outer-cauchy =
    powerSeriesIsAbsolutelyCauchyByCoefficientMajorant
      coefficients coefficients
      inner-radius outer-radius
      (nonnegativeCoefficientsSelfMajorized
        coefficients nonnegative)
      nonnegative
      abs-inner≤outer
      outer-cauchy
  where
  abs-inner≤outer :
    absℝ inner-radius ≤ℝ outer-radius
  abs-inner≤outer =
    subst
      (_≤ℝ outer-radius)
      (sym
        (absOfNonnegative
          inner-radius inner-nonnegative))
      inner≤outer

nonnegativePowerSeriesIsCauchyWithinRadius :
  ∀ coefficients inner-radius outer-radius →
  NonnegativeCoefficients coefficients →
  0 ≤ℝ inner-radius →
  inner-radius ≤ℝ outer-radius →
  IsCauchySeries
    (powerSeriesTerms coefficients outer-radius) →
  IsCauchySeries
    (powerSeriesTerms coefficients inner-radius)
nonnegativePowerSeriesIsCauchyWithinRadius
  coefficients inner-radius outer-radius
  nonnegative inner-nonnegative inner≤outer outer-cauchy =
    absoluteCauchySeriesIsCauchy
      (powerSeriesTerms coefficients inner-radius)
      (nonnegativePowerSeriesIsAbsolutelyCauchyWithinRadius
        coefficients inner-radius outer-radius
        nonnegative inner-nonnegative inner≤outer
        outer-cauchy)

nonnegativePowerSeriesIsCauchyWithinStrictRadius :
  ∀ coefficients inner-radius outer-radius →
  NonnegativeCoefficients coefficients →
  0 ≤ℝ inner-radius →
  inner-radius <ℝ outer-radius →
  IsCauchySeries
    (powerSeriesTerms coefficients outer-radius) →
  IsCauchySeries
    (powerSeriesTerms coefficients inner-radius)
nonnegativePowerSeriesIsCauchyWithinStrictRadius
  coefficients inner-radius outer-radius
  nonnegative inner-nonnegative inner<outer =
    nonnegativePowerSeriesIsCauchyWithinRadius
      coefficients inner-radius outer-radius
      nonnegative inner-nonnegative
      (<ℝ-weaken
        inner-radius outer-radius inner<outer)

powerSeriesAbsoluteSumLeCoefficientMajorant :
  ∀ coefficients majorant x radius →
  (coefficients-majorized :
    CoefficientMajorizedBy
      coefficients majorant) →
  (majorant-nonnegative :
    NonnegativeCoefficients majorant) →
  (absx≤radius :
    absℝ x ≤ℝ radius) →
  (absolute :
    IsAbsolutelyCauchySeries
      (powerSeriesTerms coefficients x)) →
  (majorant-summable :
    Summable
      (powerSeriesTerms majorant radius)) →
  seriesSum
      (absℝ ∘
        powerSeriesTerms coefficients x)
      (absoluteCauchySeriesIsAbsolutelySummable
        (powerSeriesTerms coefficients x)
        absolute)
    ≤ℝ
  seriesSum
      (powerSeriesTerms majorant radius)
      majorant-summable
powerSeriesAbsoluteSumLeCoefficientMajorant
  coefficients majorant x radius
  coefficients-majorized
  majorant-nonnegative
  absx≤radius
  absolute majorant-summable =
    seriesSumMono
      (absℝ ∘
        powerSeriesTerms coefficients x)
      (powerSeriesTerms majorant radius)
      (absoluteCauchySeriesIsAbsolutelySummable
        (powerSeriesTerms coefficients x)
        absolute)
      majorant-summable
      (powerSeriesTermAbsBoundByCoefficientMajorant
        coefficients majorant x radius
        coefficients-majorized
        majorant-nonnegative
        absx≤radius)

powerSeriesAbsoluteSumBoundByCoefficientMajorant :
  ∀ B coefficients majorant x radius →
  (coefficients-majorized :
    CoefficientMajorizedBy
      coefficients majorant) →
  (majorant-nonnegative :
    NonnegativeCoefficients majorant) →
  (absx≤radius :
    absℝ x ≤ℝ radius) →
  (absolute :
    IsAbsolutelyCauchySeries
      (powerSeriesTerms coefficients x)) →
  (majorant-summable :
    Summable
      (powerSeriesTerms majorant radius)) →
  seriesSum
      (powerSeriesTerms majorant radius)
      majorant-summable
    ≤ℝ rat (fst B) →
  AbsoluteCauchySeriesSumBound
    B
    (powerSeriesTerms coefficients x)
    absolute
powerSeriesAbsoluteSumBoundByCoefficientMajorant
  B coefficients majorant x radius
  coefficients-majorized
  majorant-nonnegative
  absx≤radius
  absolute majorant-summable
  majorant-sum-bounded =
    ≤ℝ-trans
      absolute-sum
      (seriesSum
        (powerSeriesTerms majorant radius)
        majorant-summable)
      (rat (fst B))
      (powerSeriesAbsoluteSumLeCoefficientMajorant
        coefficients majorant x radius
        coefficients-majorized
        majorant-nonnegative
        absx≤radius
        absolute majorant-summable)
      majorant-sum-bounded
  where
  absolute-sum : ℝ
  absolute-sum =
    seriesSum
      (absℝ ∘
        powerSeriesTerms coefficients x)
      (absoluteCauchySeriesIsAbsolutelySummable
        (powerSeriesTerms coefficients x)
        absolute)
