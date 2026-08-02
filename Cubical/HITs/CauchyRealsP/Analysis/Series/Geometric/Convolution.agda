module Cubical.HITs.CauchyRealsP.Analysis.Series.Geometric.Convolution where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Rationals.Inverse
open import Cubical.Data.Rationals.Order as ℚ

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Series.Base
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Absolute
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Convolution
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Convolution.Mertens
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Geometric.Base
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Geometric.Rational
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Geometric.Convergence
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Geometric.Comparison

private
  module ℚOrder =
    OrderedCommRingTheory ℚOrderedCommRing

rationalGeometricSumBound :
  ∀ (q : ℚ₊) →
  fst q ℚ.< 1 →
  ℚ₊
rationalGeometricSumBound q q<1 =
  (1 ℚ.- fst q
  , ℚOrder.<→0<Δ (fst q) 1 q<1)
  ⁻¹₊

geometricContractionSumBound :
  ∀ x →
  RationalContractionBound x →
  ℚ₊
geometricContractionSumBound x bound =
  rationalGeometricSumBound
    (fst bound)
    (snd (snd bound))

rationalGeometricSeriesCauchy :
  ∀ (q : ℚ₊) →
  (q<1 : fst q ℚ.< 1) →
  IsCauchySeries
    (geometricTerms (rat (fst q)))
rationalGeometricSeriesCauchy q q<1 =
  positiveRationalGeometricSeriesIsCauchy
    q q<1

rationalGeometricSeriesSummable :
  ∀ (q : ℚ₊) →
  (q<1 : fst q ℚ.< 1) →
  Summable
    (geometricTerms (rat (fst q)))
rationalGeometricSeriesSummable q q<1 =
  cauchySeriesIsSummable
    (geometricTerms (rat (fst q)))
    (rationalGeometricSeriesCauchy q q<1)

geometricAbsoluteCauchy :
  ∀ x →
  RationalContractionBound x →
  IsAbsolutelyCauchySeries
    (geometricTerms x)
geometricAbsoluteCauchy =
  geometricSeriesIsAbsolutelyCauchyByRationalContraction

geometricAbsoluteSummable :
  ∀ x →
  (bound : RationalContractionBound x) →
  AbsolutelySummable (geometricTerms x)
geometricAbsoluteSummable x bound =
  absoluteCauchySeriesIsAbsolutelySummable
    (geometricTerms x)
    (geometricAbsoluteCauchy x bound)

geometricCanonicalSummable :
  ∀ x →
  (bound : RationalContractionBound x) →
  Summable (geometricTerms x)
geometricCanonicalSummable x bound =
  absoluteCauchySeriesIsSummable
    (geometricTerms x)
    (geometricAbsoluteCauchy x bound)

rationalGeometricSeriesSumValue :
  ∀ (q : ℚ₊) →
  (q<1 : fst q ℚ.< 1) →
  seriesSum
    (geometricTerms (rat (fst q)))
    (rationalGeometricSeriesSummable
      q q<1)
    ≡
  rat (fst (rationalGeometricSumBound q q<1))
rationalGeometricSeriesSumValue q q<1 =
  seriesSum-geometric
    (rat (fst q))
    ratq<1
    (rationalGeometricPowersTendToZero
      (fst q)
      (ℚ.<Weaken≤
        0 (fst q) (snd q))
      q<1)
    rational-summable
  ∙ reciprocalPath
  where
  gap : ℚ
  gap =
    1 ℚ.- fst q

  gapPositive : 0 ℚ.< gap
  gapPositive =
    ℚOrder.<→0<Δ
      (fst q) 1 q<1

  denominatorPath :
    1 - rat (fst q) ≡ rat gap
  denominatorPath =
    sub-rat 1 (fst q)

  ratq<1 :
    rat (fst q) <ℝ 1
  ratq<1 =
    <ℚ→<ℝ (fst q) 1 q<1

  positiveDenominator :
    0 <ℝ 1 - rat (fst q)
  positiveDenominator =
    positiveSub
      (rat (fst q)) 1 ratq<1

  rational-summable :
    Summable
      (geometricTerms (rat (fst q)))
  rational-summable =
    rationalGeometricSeriesSummable
      q q<1

  reciprocalPath :
    positiveReciprocal
      (1 - rat (fst q))
      positiveDenominator
      ≡
    rat (fst (rationalGeometricSumBound
      q q<1))
  reciprocalPath =
    subst
      (λ z →
        (positive : 0 <ℝ z) →
        positiveReciprocal z positive
          ≡
        rat (fst (rationalGeometricSumBound
          q q<1)))
      (sym denominatorPath)
      (positiveReciprocal-rat
        gap gapPositive)
      positiveDenominator

geometricAbsoluteSeriesSumBound :
  ∀ x →
  (bound : RationalContractionBound x) →
  AbsoluteCauchySeriesSumBound
    (geometricContractionSumBound x bound)
    (geometricTerms x)
    (geometricAbsoluteCauchy x bound)
geometricAbsoluteSeriesSumBound
  x bound@(q , absx<q , q<1) =
    subst
      (absoluteSum ≤ℝ_)
      (rationalGeometricSeriesSumValue
        q q<1)
      (seriesSumMono
        (absℝ ∘ geometricTerms x)
        (geometricTerms (rat (fst q)))
        absolute-summable
        rational-summable
        dominates)
  where
  absolute :
    IsAbsolutelyCauchySeries
      (geometricTerms x)
  absolute =
    geometricAbsoluteCauchy x bound

  absolute-summable :
    AbsolutelySummable (geometricTerms x)
  absolute-summable =
    geometricAbsoluteSummable x bound

  rational-summable :
    Summable
      (geometricTerms (rat (fst q)))
  rational-summable =
    rationalGeometricSeriesSummable
      q q<1

  absoluteSum : ℝ
  absoluteSum =
    seriesSum
      (absℝ ∘ geometricTerms x)
      absolute-summable

  absx≤q :
    absℝ x ≤ℝ rat (fst q)
  absx≤q =
    <ℝ-weaken
      (absℝ x) (rat (fst q))
      absx<q

  dominates : ∀ n →
    absℝ (geometricTerms x n)
      ≤ℝ
    geometricTerms (rat (fst q)) n
  dominates n =
    subst
      (_≤ℝ
        geometricTerms (rat (fst q)) n)
      (sym (absPow n x))
      (powMonoℝ n
        (absNonnegative x)
        absx≤q)

seriesSum-geometricByRationalContraction :
  ∀ x →
  (bound : RationalContractionBound x) →
  (summable : Summable (geometricTerms x)) →
  seriesSum
    (geometricTerms x)
    summable
    ≡
  positiveReciprocal
    (1 - x)
    (positiveSub x 1
      (rationalContractionBound→x<1
        x bound))
seriesSum-geometricByRationalContraction
  x bound summable =
    seriesSumIndependent
      (geometricTerms x)
      summable
      ( reciprocal
      , geometricSeriesHasSumByRationalContraction
          x bound
      )
  where
  reciprocal : ℝ
  reciprocal =
    positiveReciprocal
      (1 - x)
      (positiveSub x 1
        (rationalContractionBound→x<1
          x bound))

geometricCauchyProductIsCauchy :
  ∀ x y →
  (x-bound : RationalContractionBound x) →
  (y-bound : RationalContractionBound y) →
  IsCauchySeries
    (cauchyProduct
      (geometricTerms x)
      (geometricTerms y))
geometricCauchyProductIsCauchy
  x y x-bound y-bound =
    absoluteMertensCauchyProductIsCauchy
      (geometricContractionSumBound
        x x-bound)
      (geometricContractionSumBound
        y y-bound)
      (geometricTerms x)
      (geometricTerms y)
      (geometricAbsoluteCauchy
        x x-bound)
      (geometricAbsoluteCauchy
        y y-bound)
      (geometricAbsoluteSeriesSumBound
        x x-bound)
      (geometricAbsoluteSeriesSumBound
        y y-bound)

geometricCauchyProductSummable :
  ∀ x y →
  (x-bound : RationalContractionBound x) →
  (y-bound : RationalContractionBound y) →
  Summable
    (cauchyProduct
      (geometricTerms x)
      (geometricTerms y))
geometricCauchyProductSummable
  x y x-bound y-bound =
    cauchySeriesIsSummable
      (cauchyProduct
        (geometricTerms x)
        (geometricTerms y))
      (geometricCauchyProductIsCauchy
        x y x-bound y-bound)

seriesSum-geometricCauchyProduct :
  ∀ x y →
  (x-bound : RationalContractionBound x) →
  (y-bound : RationalContractionBound y) →
  (product-summable :
    Summable
      (cauchyProduct
        (geometricTerms x)
        (geometricTerms y))) →
  seriesSum
    (cauchyProduct
      (geometricTerms x)
      (geometricTerms y))
    product-summable
    ≡
  positiveReciprocal
    (1 - x)
    (positiveSub x 1
      (rationalContractionBound→x<1
        x x-bound))
  ·
  positiveReciprocal
    (1 - y)
    (positiveSub y 1
      (rationalContractionBound→x<1
        y y-bound))
seriesSum-geometricCauchyProduct
  x y x-bound y-bound product-summable =
    absoluteMertensSeriesSum-cauchyProduct
      (geometricContractionSumBound
        x x-bound)
      (geometricContractionSumBound
        y y-bound)
      (geometricTerms x)
      (geometricTerms y)
      (geometricAbsoluteCauchy
        x x-bound)
      (geometricAbsoluteCauchy
        y y-bound)
      (geometricAbsoluteSeriesSumBound
        x x-bound)
      (geometricAbsoluteSeriesSumBound
        y y-bound)
      product-summable
  ∙ cong₂ _·_
      (seriesSum-geometricByRationalContraction
        x x-bound
        (geometricCanonicalSummable
          x x-bound))
      (seriesSum-geometricByRationalContraction
        y y-bound
        (geometricCanonicalSummable
          y y-bound))
