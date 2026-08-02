module Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Convergence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Sequence
open import Cubical.HITs.CauchyRealsP.Analysis.Series.Base
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Absolute
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Operations
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Bounds
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Convolution.Mertens
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Geometric.Base
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Geometric.Comparison
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Geometric.Convolution
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Base

coefficientGeometricMajorant :
  ℚ₊ → ℚ₊ → RealSequence
coefficientGeometricMajorant C q =
  scaleSeries
    (rat (fst C))
    (geometricTerms (rat (fst q)))

powerSeriesTermAbsBound :
  ∀ C q coefficients x →
  CoefficientAbsBound C coefficients →
  absℝ x ≤ℝ rat (fst q) →
  ∀ n →
  absℝ (powerSeriesTerms coefficients x n)
    ≤ℝ
  coefficientGeometricMajorant C q n
powerSeriesTermAbsBound
  C q coefficients x
  coefficients-bounded absx≤q n =
    subst
      (_≤ℝ
        coefficientGeometricMajorant C q n)
      (sym absolute-term-path)
      product-bound
  where
  absolute-term-path :
    absℝ (powerSeriesTerms coefficients x n)
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

  power-bound :
    absℝ x ^ⁿ n
      ≤ℝ
    rat (fst q) ^ⁿ n
  power-bound =
    powMonoℝ n
      (absNonnegative x)
      absx≤q

  product-bound :
    absℝ (coefficients n)
      · absℝ x ^ⁿ n
      ≤ℝ
    coefficientGeometricMajorant C q n
  product-bound =
    mulMono≤
      (absℝ (coefficients n))
      (rat (fst C))
      (absℝ x ^ⁿ n)
      (rat (fst q) ^ⁿ n)
      (positiveRationalNonnegative C)
      (powNonnegativeℝ
        (absℝ x) n
        (absNonnegative x))
      (coefficients-bounded n)
      power-bound

coefficientGeometricMajorantIsCauchy :
  ∀ C q →
  fst q ℚ.< 1 →
  IsCauchySeries
    (coefficientGeometricMajorant C q)
coefficientGeometricMajorantIsCauchy
  C q q<1 =
    rationalScaleSeriesIsCauchy
      (fst C)
      (geometricTerms (rat (fst q)))
      (positiveRationalGeometricSeriesIsCauchy
        q q<1)

coefficientGeometricMajorantSummable :
  ∀ C q →
  (q<1 : fst q ℚ.< 1) →
  Summable
    (coefficientGeometricMajorant C q)
coefficientGeometricMajorantSummable
  C q q<1 =
    scaleSummable
      (rat (fst C))
      (geometricTerms (rat (fst q)))
      (rationalGeometricSeriesSummable
        q q<1)

seriesSum-coefficientGeometricMajorant :
  ∀ C q →
  (q<1 : fst q ℚ.< 1) →
  (majorant-summable :
    Summable
      (coefficientGeometricMajorant C q)) →
  seriesSum
      (coefficientGeometricMajorant C q)
      majorant-summable
    ≡
  rat
    (fst
      (C ·₊
        rationalGeometricSumBound q q<1))
seriesSum-coefficientGeometricMajorant
  C q q<1 majorant-summable =
    seriesSum-scale
      (rat (fst C))
      (geometricTerms (rat (fst q)))
      (rationalGeometricSeriesSummable
        q q<1)
      majorant-summable
  ∙ cong
      (rat (fst C) ·_)
      (rationalGeometricSeriesSumValue
        q q<1)
  ∙ mul-rat
      (fst C)
      (fst
        (rationalGeometricSumBound q q<1))

powerSeriesIsAbsolutelyCauchyByMajorant :
  ∀ C q coefficients x →
  CoefficientAbsBound C coefficients →
  absℝ x ≤ℝ rat (fst q) →
  fst q ℚ.< 1 →
  IsAbsolutelyCauchySeries
    (powerSeriesTerms coefficients x)
powerSeriesIsAbsolutelyCauchyByMajorant
  C q coefficients x
  coefficients-bounded absx≤q q<1 =
    dominatedCauchySeriesIsCauchy
      (absℝ ∘
        powerSeriesTerms coefficients x)
      (coefficientGeometricMajorant C q)
      dominates
      (coefficientGeometricMajorantIsCauchy
        C q q<1)
  where
  dominates : ∀ n →
    absℝ
      (absℝ
        (powerSeriesTerms coefficients x n))
      ≤ℝ
    coefficientGeometricMajorant C q n
  dominates n =
    subst
      (_≤ℝ
        coefficientGeometricMajorant C q n)
      (sym
        (absIdem
          (powerSeriesTerms coefficients x n)))
      (powerSeriesTermAbsBound
        C q coefficients x
        coefficients-bounded absx≤q n)

powerSeriesIsAbsolutelyCauchy :
  ∀ C coefficients x →
  CoefficientAbsBound C coefficients →
  RationalContractionBound x →
  IsAbsolutelyCauchySeries
    (powerSeriesTerms coefficients x)
powerSeriesIsAbsolutelyCauchy
  C coefficients x
  coefficients-bounded
  (q , absx<q , q<1) =
    powerSeriesIsAbsolutelyCauchyByMajorant
      C q coefficients x
      coefficients-bounded
      (<ℝ-weaken
        (absℝ x)
        (rat (fst q))
        absx<q)
      q<1

powerSeriesIsCauchy :
  ∀ C coefficients x →
  CoefficientAbsBound C coefficients →
  RationalContractionBound x →
  IsCauchySeries
    (powerSeriesTerms coefficients x)
powerSeriesIsCauchy
  C coefficients x
  coefficients-bounded contraction =
    absoluteCauchySeriesIsCauchy
      (powerSeriesTerms coefficients x)
      (powerSeriesIsAbsolutelyCauchy
        C coefficients x
        coefficients-bounded contraction)

powerSeriesIsSummable :
  ∀ C coefficients x →
  CoefficientAbsBound C coefficients →
  RationalContractionBound x →
  PowerSeriesSummableAt coefficients x
powerSeriesIsSummable
  C coefficients x
  coefficients-bounded contraction =
    absoluteCauchySeriesIsSummable
      (powerSeriesTerms coefficients x)
      (powerSeriesIsAbsolutelyCauchy
        C coefficients x
        coefficients-bounded contraction)

powerSeriesAbsoluteSumBoundByMajorant :
  ∀ C q coefficients x →
  (coefficients-bounded :
    CoefficientAbsBound C coefficients) →
  (absx≤q :
    absℝ x ≤ℝ rat (fst q)) →
  (q<1 : fst q ℚ.< 1) →
  (absolute :
    IsAbsolutelyCauchySeries
      (powerSeriesTerms coefficients x)) →
  AbsoluteCauchySeriesSumBound
    (C ·₊ rationalGeometricSumBound q q<1)
    (powerSeriesTerms coefficients x)
    absolute
powerSeriesAbsoluteSumBoundByMajorant
  C q coefficients x
  coefficients-bounded absx≤q q<1
  absolute =
    subst
      (absolute-sum ≤ℝ_)
      (seriesSum-coefficientGeometricMajorant
        C q q<1 majorant-summable)
      (seriesSumMono
        (absℝ ∘
          powerSeriesTerms coefficients x)
        (coefficientGeometricMajorant C q)
        absolute-summable
        majorant-summable
        (powerSeriesTermAbsBound
          C q coefficients x
          coefficients-bounded absx≤q))
  where
  absolute-summable :
    AbsolutelySummable
      (powerSeriesTerms coefficients x)
  absolute-summable =
    absoluteCauchySeriesIsAbsolutelySummable
      (powerSeriesTerms coefficients x)
      absolute

  majorant-summable :
    Summable
      (coefficientGeometricMajorant C q)
  majorant-summable =
    coefficientGeometricMajorantSummable
      C q q<1

  absolute-sum : ℝ
  absolute-sum =
    seriesSum
      (absℝ ∘
        powerSeriesTerms coefficients x)
      absolute-summable

powerSeriesContractionSumBound :
  ℚ₊ → (x : ℝ) →
  RationalContractionBound x →
  ℚ₊
powerSeriesContractionSumBound C x contraction =
  C ·₊
    geometricContractionSumBound
      x contraction

powerSeriesAbsoluteSumBound :
  ∀ C coefficients x →
  (coefficients-bounded :
    CoefficientAbsBound C coefficients) →
  (contraction :
    RationalContractionBound x) →
  AbsoluteCauchySeriesSumBound
    (powerSeriesContractionSumBound
      C x contraction)
    (powerSeriesTerms coefficients x)
    (powerSeriesIsAbsolutelyCauchy
      C coefficients x
      coefficients-bounded contraction)
powerSeriesAbsoluteSumBound
  C coefficients x
  coefficients-bounded
  contraction@(q , absx<q , q<1) =
    powerSeriesAbsoluteSumBoundByMajorant
      C q coefficients x
      coefficients-bounded
      (<ℝ-weaken
        (absℝ x)
        (rat (fst q))
        absx<q)
      q<1
      (powerSeriesIsAbsolutelyCauchy
        C coefficients x
        coefficients-bounded contraction)

powerSeriesIsAbsolutelySummable :
  ∀ C coefficients x →
  CoefficientAbsBound C coefficients →
  RationalContractionBound x →
  AbsolutelySummable
    (powerSeriesTerms coefficients x)
powerSeriesIsAbsolutelySummable
  C coefficients x
  coefficients-bounded contraction =
    absoluteCauchySeriesIsAbsolutelySummable
      (powerSeriesTerms coefficients x)
      (powerSeriesIsAbsolutelyCauchy
        C coefficients x
        coefficients-bounded contraction)
