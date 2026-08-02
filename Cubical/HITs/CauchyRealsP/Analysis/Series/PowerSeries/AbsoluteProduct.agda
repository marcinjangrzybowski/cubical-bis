module Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.AbsoluteProduct where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Sequence
open import Cubical.HITs.CauchyRealsP.Analysis.Series.Base
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Absolute
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Convolution
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Convolution.Mertens
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Convolution.Absolute
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Base
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Product

powerSeriesCauchyProductIsAbsolutelyCauchyByBounds :
  ∀ (A B : ℚ₊)
    (a b : RealSequence) (x : ℝ) →
  (a-absolute :
    IsAbsolutelyCauchySeries
      (powerSeriesTerms a x)) →
  (b-absolute :
    IsAbsolutelyCauchySeries
      (powerSeriesTerms b x)) →
  AbsoluteCauchySeriesSumBound
    A (powerSeriesTerms a x)
    a-absolute →
  AbsoluteCauchySeriesSumBound
    B (powerSeriesTerms b x)
    b-absolute →
  IsAbsolutelyCauchySeries
    (powerSeriesTerms
      (cauchyProduct a b) x)
powerSeriesCauchyProductIsAbsolutelyCauchyByBounds
  A B a b x
  a-absolute b-absolute
  a-sum-bounded b-sum-bounded =
    subst
      IsAbsolutelyCauchySeries
      (sym coefficient-product-path)
      term-product-absolute
  where
  coefficient-product-path :
    powerSeriesTerms
        (cauchyProduct a b) x
      ≡
    cauchyProduct
      (powerSeriesTerms a x)
      (powerSeriesTerms b x)
  coefficient-product-path =
    powerSeriesTerms-cauchyProduct-sequence
      a b x

  term-product-absolute :
    IsAbsolutelyCauchySeries
      (cauchyProduct
        (powerSeriesTerms a x)
        (powerSeriesTerms b x))
  term-product-absolute =
    absoluteMertensCauchyProductIsAbsolutelyCauchy
      A B
      (powerSeriesTerms a x)
      (powerSeriesTerms b x)
      a-absolute b-absolute
      a-sum-bounded b-sum-bounded

powerSeriesCauchyProductAbsoluteSumBound :
  ∀ (A B : ℚ₊)
    (a b : RealSequence) (x : ℝ)
    (a-absolute :
      IsAbsolutelyCauchySeries
        (powerSeriesTerms a x))
    (b-absolute :
      IsAbsolutelyCauchySeries
        (powerSeriesTerms b x)) →
  (a-sum-bounded :
    AbsoluteCauchySeriesSumBound
      A (powerSeriesTerms a x)
      a-absolute) →
  (b-sum-bounded :
    AbsoluteCauchySeriesSumBound
      B (powerSeriesTerms b x)
      b-absolute) →
  (product-absolute :
    IsAbsolutelyCauchySeries
      (powerSeriesTerms
        (cauchyProduct a b) x)) →
  AbsoluteCauchySeriesSumBound
    (A ·₊ B)
    (powerSeriesTerms
      (cauchyProduct a b) x)
    product-absolute
powerSeriesCauchyProductAbsoluteSumBound
  A B a b x
  a-absolute b-absolute
  a-sum-bounded b-sum-bounded
  product-absolute =
    absoluteCauchySeriesSumBoundPresPath
      (A ·₊ B)
      (sym coefficient-product-path)
      term-product-absolute
      product-absolute
      term-product-sum-bounded
  where
  coefficient-product-path :
    powerSeriesTerms
        (cauchyProduct a b) x
      ≡
    cauchyProduct
      (powerSeriesTerms a x)
      (powerSeriesTerms b x)
  coefficient-product-path =
    powerSeriesTerms-cauchyProduct-sequence
      a b x

  term-product-absolute :
    IsAbsolutelyCauchySeries
      (cauchyProduct
        (powerSeriesTerms a x)
        (powerSeriesTerms b x))
  term-product-absolute =
    absoluteMertensCauchyProductIsAbsolutelyCauchy
      A B
      (powerSeriesTerms a x)
      (powerSeriesTerms b x)
      a-absolute b-absolute
      a-sum-bounded b-sum-bounded

  term-product-sum-bounded :
    AbsoluteCauchySeriesSumBound
      (A ·₊ B)
      (cauchyProduct
        (powerSeriesTerms a x)
        (powerSeriesTerms b x))
      term-product-absolute
  term-product-sum-bounded =
    absoluteMertensCauchyProductAbsoluteSumBound
      A B
      (powerSeriesTerms a x)
      (powerSeriesTerms b x)
      a-absolute b-absolute
      a-sum-bounded b-sum-bounded
      term-product-absolute

powerSeriesCauchyProductSummableByAbsoluteBounds :
  ∀ (A B : ℚ₊)
    (a b : RealSequence) (x : ℝ) →
  (a-absolute :
    IsAbsolutelyCauchySeries
      (powerSeriesTerms a x)) →
  (b-absolute :
    IsAbsolutelyCauchySeries
      (powerSeriesTerms b x)) →
  AbsoluteCauchySeriesSumBound
    A (powerSeriesTerms a x)
    a-absolute →
  AbsoluteCauchySeriesSumBound
    B (powerSeriesTerms b x)
    b-absolute →
  PowerSeriesSummableAt
    (cauchyProduct a b) x
powerSeriesCauchyProductSummableByAbsoluteBounds
  A B a b x
  a-absolute b-absolute
  a-sum-bounded b-sum-bounded =
    absoluteCauchySeriesIsSummable
      (powerSeriesTerms
        (cauchyProduct a b) x)
      (powerSeriesCauchyProductIsAbsolutelyCauchyByBounds
        A B a b x
        a-absolute b-absolute
        a-sum-bounded b-sum-bounded)

powerSeriesValue-cauchyProductByAbsoluteBounds :
  ∀ (A B : ℚ₊)
    (a b : RealSequence) (x : ℝ) →
  (a-absolute :
    IsAbsolutelyCauchySeries
      (powerSeriesTerms a x)) →
  (b-absolute :
    IsAbsolutelyCauchySeries
      (powerSeriesTerms b x)) →
  AbsoluteCauchySeriesSumBound
    A (powerSeriesTerms a x)
    a-absolute →
  AbsoluteCauchySeriesSumBound
    B (powerSeriesTerms b x)
    b-absolute →
  (a-summable :
    PowerSeriesSummableAt a x) →
  (b-summable :
    PowerSeriesSummableAt b x) →
  (product-summable :
    PowerSeriesSummableAt
      (cauchyProduct a b) x) →
  powerSeriesValue
      (cauchyProduct a b) x
      product-summable
    ≡
  powerSeriesValue a x a-summable
    · powerSeriesValue b x b-summable
powerSeriesValue-cauchyProductByAbsoluteBounds
  A B a b x
  a-absolute b-absolute
  a-sum-bounded b-sum-bounded
  a-summable b-summable
  product-summable =
    seriesSumIndependent
      coefficient-product-terms
      product-summable
      target-summable
  where
  a-terms : RealSequence
  a-terms =
    powerSeriesTerms a x

  b-terms : RealSequence
  b-terms =
    powerSeriesTerms b x

  coefficient-product-terms :
    RealSequence
  coefficient-product-terms =
    powerSeriesTerms
      (cauchyProduct a b) x

  a-uniform :
    UniformAbsolutePartialSumBound
      A a-terms
  a-uniform =
    absoluteCauchySumBound→uniformAbsoluteBound
      A a-terms a-absolute
      a-sum-bounded

  b-uniform :
    UniformAbsolutePartialSumBound
      B b-terms
  b-uniform =
    absoluteCauchySumBound→uniformAbsoluteBound
      B b-terms b-absolute
      b-sum-bounded

  approximation :
    CauchyProductRectangularApproximation
      a-terms b-terms
  approximation =
    mertensRectangularApproximation
      A B a-terms b-terms
      a-uniform
      (uniformAbsoluteBound→uniformBound
        B b-terms b-uniform)
      a-absolute
      (absoluteCauchySeriesIsCauchy
        b-terms b-absolute)

  target : ℝ
  target =
    powerSeriesValue a x a-summable
      · powerSeriesValue b x b-summable

  term-product-has-sum :
    HasSum
      (cauchyProduct a-terms b-terms)
      target
  term-product-has-sum =
    cauchyProductHasSum
      a-terms b-terms
      (powerSeriesValue a x a-summable)
      (powerSeriesValue b x b-summable)
      (seriesSumHasSum
        a-terms a-summable)
      (seriesSumHasSum
        b-terms b-summable)
      approximation

  coefficient-product-has-sum :
    HasSum coefficient-product-terms target
  coefficient-product-has-sum =
    subst
      (λ terms → HasSum terms target)
      (sym
        (powerSeriesTerms-cauchyProduct-sequence
          a b x))
      term-product-has-sum

  target-summable :
    Summable coefficient-product-terms
  target-summable =
    target
    , coefficient-product-has-sum

PowerSeriesAbsoluteWithBound :
  ℚ₊ → RealSequence → ℝ → Type
PowerSeriesAbsoluteWithBound
  B coefficients x =
    AbsoluteCauchySeriesWithBound
      B (powerSeriesTerms coefficients x)

opaque
  powerSeriesCauchyProductWithBound :
    ∀ (A B : ℚ₊)
      (a b : RealSequence) (x : ℝ) →
    PowerSeriesAbsoluteWithBound A a x →
    PowerSeriesAbsoluteWithBound B b x →
    PowerSeriesAbsoluteWithBound
      (A ·₊ B)
      (cauchyProduct a b)
      x
  powerSeriesCauchyProductWithBound
    A B a b x
    a-data b-data =
      coefficient-product-absolute
      ,
      absoluteCauchySeriesSumBoundPresPath
        (A ·₊ B)
        (sym coefficient-product-path)
        (fst term-product-data)
        coefficient-product-absolute
        (snd term-product-data)
    where
    coefficient-product-path :
      powerSeriesTerms
          (cauchyProduct a b) x
        ≡
      cauchyProduct
        (powerSeriesTerms a x)
        (powerSeriesTerms b x)
    coefficient-product-path =
      powerSeriesTerms-cauchyProduct-sequence
        a b x

    term-product-data :
      AbsoluteCauchySeriesWithBound
        (A ·₊ B)
        (cauchyProduct
          (powerSeriesTerms a x)
          (powerSeriesTerms b x))
    term-product-data =
      absoluteMertensCauchyProductWithBound
        A B
        (powerSeriesTerms a x)
        (powerSeriesTerms b x)
        a-data b-data

    coefficient-product-absolute :
      IsAbsolutelyCauchySeries
        (powerSeriesTerms
          (cauchyProduct a b) x)
    coefficient-product-absolute =
      subst
        IsAbsolutelyCauchySeries
        (sym coefficient-product-path)
        (fst term-product-data)

  powerSeriesValue-cauchyProductWithBound :
    ∀ (A B : ℚ₊)
      (a b : RealSequence) (x : ℝ) →
    (a-data :
      PowerSeriesAbsoluteWithBound A a x) →
    (b-data :
      PowerSeriesAbsoluteWithBound B b x) →
    (a-summable :
      PowerSeriesSummableAt a x) →
    (b-summable :
      PowerSeriesSummableAt b x) →
    (product-summable :
      PowerSeriesSummableAt
        (cauchyProduct a b) x) →
    powerSeriesValue
        (cauchyProduct a b) x
        product-summable
      ≡
    powerSeriesValue a x a-summable
      · powerSeriesValue b x b-summable
  powerSeriesValue-cauchyProductWithBound
    A B a b x
    a-data b-data
    a-summable b-summable
    product-summable =
      powerSeriesValue-cauchyProductByAbsoluteBounds
        A B a b x
        (fst a-data)
        (fst b-data)
        (snd a-data)
        (snd b-data)
        a-summable b-summable
        product-summable
