module Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Operations where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Sequence
open import Cubical.HITs.CauchyRealsP.Analysis.Series.Base
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Operations
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Bounds
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Geometric.Comparison
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Base
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Convergence

addCoefficientAbsBound :
  ∀ A B a b →
  CoefficientAbsBound A a →
  CoefficientAbsBound B b →
  CoefficientAbsBound
    (A +₊ B)
    (λ n → a n + b n)
addCoefficientAbsBound
  A B a b a-bounded b-bounded n =
    subst
      (absℝ (a n + b n) ≤ℝ_)
      (rat+rat (fst A) (fst B))
      (≤ℝ-trans
        (absℝ (a n + b n))
        (absℝ (a n) + absℝ (b n))
        (rat (fst A) + rat (fst B))
        (absTriangle (a n) (b n))
        (≤ℝ-add
          (absℝ (a n)) (rat (fst A))
          (absℝ (b n)) (rat (fst B))
          (a-bounded n)
          (b-bounded n)))

scaleCoefficientAbsBound :
  ∀ C B c coefficients →
  absℝ c ≤ℝ rat (fst C) →
  CoefficientAbsBound B coefficients →
  CoefficientAbsBound
    (C ·₊ B)
    (scaleSeries c coefficients)
scaleCoefficientAbsBound
  C B c coefficients
  c-bounded coefficients-bounded n =
    subst
      (absℝ
        (scaleSeries c coefficients n)
        ≤ℝ_)
      (mul-rat (fst C) (fst B))
      (subst
        (_≤ℝ
          rat (fst C) · rat (fst B))
        (sym
          (absMul c (coefficients n)))
        (mulMono≤
          (absℝ c)
          (rat (fst C))
          (absℝ (coefficients n))
          (rat (fst B))
          (positiveRationalNonnegative C)
          (absNonnegative (coefficients n))
          c-bounded
          (coefficients-bounded n)))

powerSeriesTerms-add-sequence :
  ∀ (a b : RealSequence) (x : ℝ) →
  powerSeriesTerms
      (λ n → a n + b n) x
    ≡
  (λ n →
    powerSeriesTerms a x n
      + powerSeriesTerms b x n)
powerSeriesTerms-add-sequence a b x =
  funExt (powerSeriesTerms-add a b x)

powerSeriesTerms-scale-sequence :
  ∀ c (coefficients : RealSequence) x →
  powerSeriesTerms
      (scaleSeries c coefficients) x
    ≡
  scaleSeries c
    (powerSeriesTerms coefficients x)
powerSeriesTerms-scale-sequence
  c coefficients x =
    funExt
      (powerSeriesTerms-scale
        c coefficients x)

powerSeriesAddSummable :
  ∀ (a b : RealSequence) x →
  PowerSeriesSummableAt a x →
  PowerSeriesSummableAt b x →
  PowerSeriesSummableAt
    (λ n → a n + b n) x
powerSeriesAddSummable
  a b x a-summable b-summable =
    subst Summable
      (sym
        (powerSeriesTerms-add-sequence
          a b x))
      (addSummable
        (powerSeriesTerms a x)
        (powerSeriesTerms b x)
        a-summable b-summable)

powerSeriesScaleSummable :
  ∀ c (coefficients : RealSequence) x →
  PowerSeriesSummableAt coefficients x →
  PowerSeriesSummableAt
    (scaleSeries c coefficients) x
powerSeriesScaleSummable
  c coefficients x summable =
    subst Summable
      (sym
        (powerSeriesTerms-scale-sequence
          c coefficients x))
      (scaleSummable
        c
        (powerSeriesTerms coefficients x)
        summable)

powerSeriesValue-add :
  ∀ (a b : RealSequence) x →
  (a-summable :
    PowerSeriesSummableAt a x) →
  (b-summable :
    PowerSeriesSummableAt b x) →
  (sum-summable :
    PowerSeriesSummableAt
      (λ n → a n + b n) x) →
  powerSeriesValue
      (λ n → a n + b n)
      x sum-summable
    ≡
  powerSeriesValue a x a-summable
    + powerSeriesValue b x b-summable
powerSeriesValue-add
  a b x
  a-summable b-summable sum-summable =
    seriesSumIndependent
      sum-terms
      sum-summable
      target-summable
  where
  sum-terms : RealSequence
  sum-terms =
    powerSeriesTerms
      (λ n → a n + b n) x

  target : ℝ
  target =
    powerSeriesValue a x a-summable
      + powerSeriesValue b x b-summable

  pointwise-sum-has-sum :
    HasSum
      (λ n →
        powerSeriesTerms a x n
          + powerSeriesTerms b x n)
      target
  pointwise-sum-has-sum =
    snd
      (addSummable
        (powerSeriesTerms a x)
        (powerSeriesTerms b x)
        a-summable b-summable)

  sum-has-sum :
    HasSum sum-terms target
  sum-has-sum =
    subst
      (λ terms → HasSum terms target)
      (sym
        (powerSeriesTerms-add-sequence
          a b x))
      pointwise-sum-has-sum

  target-summable :
    Summable sum-terms
  target-summable =
    target , sum-has-sum

powerSeriesValue-scale :
  ∀ c (coefficients : RealSequence) x →
  (summable :
    PowerSeriesSummableAt coefficients x) →
  (scaled-summable :
    PowerSeriesSummableAt
      (scaleSeries c coefficients) x) →
  powerSeriesValue
      (scaleSeries c coefficients)
      x scaled-summable
    ≡
  c · powerSeriesValue
      coefficients x summable
powerSeriesValue-scale
  c coefficients x
  summable scaled-summable =
    seriesSumIndependent
      scaled-terms
      scaled-summable
      target-summable
  where
  scaled-terms : RealSequence
  scaled-terms =
    powerSeriesTerms
      (scaleSeries c coefficients) x

  target : ℝ
  target =
    c · powerSeriesValue
      coefficients x summable

  pointwise-scaled-has-sum :
    HasSum
      (scaleSeries c
        (powerSeriesTerms coefficients x))
      target
  pointwise-scaled-has-sum =
    snd
      (scaleSummable
        c
        (powerSeriesTerms coefficients x)
        summable)

  scaled-has-sum :
    HasSum scaled-terms target
  scaled-has-sum =
    subst
      (λ terms → HasSum terms target)
      (sym
        (powerSeriesTerms-scale-sequence
          c coefficients x))
      pointwise-scaled-has-sum

  target-summable :
    Summable scaled-terms
  target-summable =
    target , scaled-has-sum

boundedPowerSeriesAddSummable :
  ∀ A B (a b : RealSequence) x →
  CoefficientAbsBound A a →
  CoefficientAbsBound B b →
  RationalContractionBound x →
  PowerSeriesSummableAt
    (λ n → a n + b n) x
boundedPowerSeriesAddSummable
  A B a b x
  a-bounded b-bounded contraction =
    powerSeriesIsSummable
      (A +₊ B)
      (λ n → a n + b n)
      x
      (addCoefficientAbsBound
        A B a b
        a-bounded b-bounded)
      contraction

boundedPowerSeriesScaleSummable :
  ∀ C B c (coefficients : RealSequence) x →
  absℝ c ≤ℝ rat (fst C) →
  CoefficientAbsBound B coefficients →
  RationalContractionBound x →
  PowerSeriesSummableAt
    (scaleSeries c coefficients) x
boundedPowerSeriesScaleSummable
  C B c coefficients x
  c-bounded coefficients-bounded contraction =
    powerSeriesIsSummable
      (C ·₊ B)
      (scaleSeries c coefficients)
      x
      (scaleCoefficientAbsBound
        C B c coefficients
        c-bounded coefficients-bounded)
      contraction
