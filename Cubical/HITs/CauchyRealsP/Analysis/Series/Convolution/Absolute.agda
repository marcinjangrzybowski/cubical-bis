module Cubical.HITs.CauchyRealsP.Analysis.Series.Convolution.Absolute where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

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

absoluteTerms-idempotent :
  ∀ (terms : RealSequence) →
  (absℝ ∘ (absℝ ∘ terms))
    ≡
  (absℝ ∘ terms)
absoluteTerms-idempotent terms =
  funExt
    (λ n → absIdem (terms n))

absoluteSequenceIsAbsolutelyCauchy :
  ∀ (terms : RealSequence) →
  IsAbsolutelyCauchySeries terms →
  IsAbsolutelyCauchySeries
    (absℝ ∘ terms)
absoluteSequenceIsAbsolutelyCauchy
  terms absolute =
    subst
      IsCauchySeries
      (sym
        (absoluteTerms-idempotent terms))
      absolute

absoluteSequencePresUniformAbsoluteBound :
  ∀ (B : ℚ₊) (terms : RealSequence) →
  UniformAbsolutePartialSumBound
    B terms →
  UniformAbsolutePartialSumBound
    B (absℝ ∘ terms)
absoluteSequencePresUniformAbsoluteBound
  B terms bounded n =
    subst
      (_≤ℝ rat (fst B))
      (sym
        (partialSum-pointwise
          (absℝ ∘ (absℝ ∘ terms))
          (absℝ ∘ terms)
          (λ k → absIdem (terms k))
          n))
      (bounded n)

absoluteCauchySeriesSumBoundIndependent :
  ∀ (B : ℚ₊) (terms : RealSequence)
    (p q :
      IsAbsolutelyCauchySeries terms) →
  AbsoluteCauchySeriesSumBound
    B terms p →
  AbsoluteCauchySeriesSumBound
    B terms q
absoluteCauchySeriesSumBoundIndependent
  B terms p q bounded =
    subst
      (_≤ℝ rat (fst B))
      (sym
        (seriesSumIndependent
          (absℝ ∘ terms)
          (absoluteCauchySeriesIsAbsolutelySummable
            terms q)
          (absoluteCauchySeriesIsAbsolutelySummable
            terms p)))
      bounded

absoluteCauchySeriesSumBoundPresPath :
  ∀ (B : ℚ₊)
    {a b : RealSequence} →
  (path : a ≡ b) →
  (a-absolute :
    IsAbsolutelyCauchySeries a) →
  (b-absolute :
    IsAbsolutelyCauchySeries b) →
  AbsoluteCauchySeriesSumBound
    B a a-absolute →
  AbsoluteCauchySeriesSumBound
    B b b-absolute
absoluteCauchySeriesSumBoundPresPath
  B {a} {b} path
  a-absolute b-absolute bounded =
    subst
      (λ terms →
        (absolute :
          IsAbsolutelyCauchySeries terms) →
        AbsoluteCauchySeriesSumBound
          B terms absolute)
      path
      (λ other-absolute →
        absoluteCauchySeriesSumBoundIndependent
          B a
          a-absolute other-absolute
          bounded)
      b-absolute

absoluteMertensCauchyProductIsAbsolutelyCauchy :
  ∀ (A B : ℚ₊)
    (a b : RealSequence) →
  (a-absolute :
    IsAbsolutelyCauchySeries a) →
  (b-absolute :
    IsAbsolutelyCauchySeries b) →
  AbsoluteCauchySeriesSumBound
    A a a-absolute →
  AbsoluteCauchySeriesSumBound
    B b b-absolute →
  IsAbsolutelyCauchySeries
    (cauchyProduct a b)
absoluteMertensCauchyProductIsAbsolutelyCauchy
  A B a b
  a-absolute b-absolute
  a-sum-bounded b-sum-bounded =
    absoluteCauchyProductFromMajorant
      a b positive-product-cauchy
  where
  a-uniform :
    UniformAbsolutePartialSumBound A a
  a-uniform =
    absoluteCauchySumBound→uniformAbsoluteBound
      A a a-absolute a-sum-bounded

  b-uniform :
    UniformAbsolutePartialSumBound B b
  b-uniform =
    absoluteCauchySumBound→uniformAbsoluteBound
      B b b-absolute b-sum-bounded

  absolute-a-uniform :
    UniformAbsolutePartialSumBound
      A (absℝ ∘ a)
  absolute-a-uniform =
    absoluteSequencePresUniformAbsoluteBound
      A a a-uniform

  absolute-b-uniform :
    UniformAbsolutePartialSumBound
      B (absℝ ∘ b)
  absolute-b-uniform =
    absoluteSequencePresUniformAbsoluteBound
      B b b-uniform

  positive-product-cauchy :
    IsCauchySeries
      (absoluteCauchyProduct a b)
  positive-product-cauchy =
    mertensCauchyProductIsCauchy
      A B
      (absℝ ∘ a)
      (absℝ ∘ b)
      absolute-a-uniform
      (uniformAbsoluteBound→uniformBound
        B (absℝ ∘ b)
        absolute-b-uniform)
      (absoluteSequenceIsAbsolutelyCauchy
        a a-absolute)
      b-absolute

absoluteMertensCauchyProductAbsoluteSumBound :
  ∀ (A B : ℚ₊)
    (a b : RealSequence)
    (a-absolute :
      IsAbsolutelyCauchySeries a)
    (b-absolute :
      IsAbsolutelyCauchySeries b) →
  (a-sum-bounded :
    AbsoluteCauchySeriesSumBound
      A a a-absolute) →
  (b-sum-bounded :
    AbsoluteCauchySeriesSumBound
      B b b-absolute) →
  (product-absolute :
    IsAbsolutelyCauchySeries
      (cauchyProduct a b)) →
  AbsoluteCauchySeriesSumBound
    (A ·₊ B)
    (cauchyProduct a b)
    product-absolute
absoluteMertensCauchyProductAbsoluteSumBound
  A B a b
  a-absolute b-absolute
  a-sum-bounded b-sum-bounded
  product-absolute =
    ≤ℝ-trans
      absolute-product-sum
      positive-product-sum
      (rat (fst (A ·₊ B)))
      absolute-product≤positive-product
      positive-product≤bound
  where
  a-absolute-summable :
    Summable (absℝ ∘ a)
  a-absolute-summable =
    absoluteCauchySeriesIsAbsolutelySummable
      a a-absolute

  b-absolute-summable :
    Summable (absℝ ∘ b)
  b-absolute-summable =
    absoluteCauchySeriesIsAbsolutelySummable
      b b-absolute

  a-uniform :
    UniformAbsolutePartialSumBound A a
  a-uniform =
    absoluteCauchySumBound→uniformAbsoluteBound
      A a a-absolute a-sum-bounded

  b-uniform :
    UniformAbsolutePartialSumBound B b
  b-uniform =
    absoluteCauchySumBound→uniformAbsoluteBound
      B b b-absolute b-sum-bounded

  absolute-a-uniform :
    UniformAbsolutePartialSumBound
      A (absℝ ∘ a)
  absolute-a-uniform =
    absoluteSequencePresUniformAbsoluteBound
      A a a-uniform

  absolute-b-uniform :
    UniformAbsolutePartialSumBound
      B (absℝ ∘ b)
  absolute-b-uniform =
    absoluteSequencePresUniformAbsoluteBound
      B b b-uniform

  positive-product-approximation :
    CauchyProductRectangularApproximation
      (absℝ ∘ a)
      (absℝ ∘ b)
  positive-product-approximation =
    mertensRectangularApproximation
      A B
      (absℝ ∘ a)
      (absℝ ∘ b)
      absolute-a-uniform
      (uniformAbsoluteBound→uniformBound
        B (absℝ ∘ b)
        absolute-b-uniform)
      (absoluteSequenceIsAbsolutelyCauchy
        a a-absolute)
      b-absolute

  positive-product-summable :
    Summable (absoluteCauchyProduct a b)
  positive-product-summable =
    cauchyProductSummable
      (absℝ ∘ a)
      (absℝ ∘ b)
      a-absolute-summable
      b-absolute-summable
      positive-product-approximation

  absolute-product-sum : ℝ
  absolute-product-sum =
    seriesSum
      (absℝ ∘ cauchyProduct a b)
      (absoluteCauchySeriesIsAbsolutelySummable
        (cauchyProduct a b)
        product-absolute)

  positive-product-sum : ℝ
  positive-product-sum =
    seriesSum
      (absoluteCauchyProduct a b)
      positive-product-summable

  absolute-product≤positive-product :
    absolute-product-sum
      ≤ℝ
    positive-product-sum
  absolute-product≤positive-product =
    seriesSumMono
      (absℝ ∘ cauchyProduct a b)
      (absoluteCauchyProduct a b)
      (absoluteCauchySeriesIsAbsolutelySummable
        (cauchyProduct a b)
        product-absolute)
      positive-product-summable
      (cauchyProductAbsBound a b)

  positive-product-sum-path :
    positive-product-sum
      ≡
    seriesSum
        (absℝ ∘ a)
        a-absolute-summable
      ·
    seriesSum
        (absℝ ∘ b)
        b-absolute-summable
  positive-product-sum-path =
    seriesSum-cauchyProduct
      (absℝ ∘ a)
      (absℝ ∘ b)
      a-absolute-summable
      b-absolute-summable
      positive-product-summable
      positive-product-approximation

  b-absolute-sum-nonnegative :
    0 ≤ℝ
    seriesSum
      (absℝ ∘ b)
      b-absolute-summable
  b-absolute-sum-nonnegative =
    seriesSumNonnegative
      (absℝ ∘ b)
      b-absolute-summable
      (λ n → absNonnegative (b n))

  rational-a-nonnegative :
    0 ≤ℝ rat (fst A)
  rational-a-nonnegative =
    ≤ℚ→≤ℝ 0 (fst A)
      (ℚ.<Weaken≤
        0 (fst A) (snd A))

  factor-product≤bound-product :
    seriesSum
        (absℝ ∘ a)
        a-absolute-summable
      ·
    seriesSum
        (absℝ ∘ b)
        b-absolute-summable
      ≤ℝ
    rat (fst A) · rat (fst B)
  factor-product≤bound-product =
    mulMono≤
      (seriesSum
        (absℝ ∘ a)
        a-absolute-summable)
      (rat (fst A))
      (seriesSum
        (absℝ ∘ b)
        b-absolute-summable)
      (rat (fst B))
      rational-a-nonnegative
      b-absolute-sum-nonnegative
      a-sum-bounded
      b-sum-bounded

  factor-product≤bound :
    seriesSum
        (absℝ ∘ a)
        a-absolute-summable
      ·
    seriesSum
        (absℝ ∘ b)
        b-absolute-summable
      ≤ℝ
    rat (fst (A ·₊ B))
  factor-product≤bound =
    subst
      ( seriesSum
          (absℝ ∘ a)
          a-absolute-summable
        ·
        seriesSum
          (absℝ ∘ b)
          b-absolute-summable
        ≤ℝ_
      )
      (mul-rat (fst A) (fst B))
      factor-product≤bound-product

  positive-product≤bound :
    positive-product-sum
      ≤ℝ
    rat (fst (A ·₊ B))
  positive-product≤bound =
    subst
      (_≤ℝ rat (fst (A ·₊ B)))
      (sym positive-product-sum-path)
      factor-product≤bound

AbsoluteCauchySeriesWithBound :
  ℚ₊ → RealSequence → Type
AbsoluteCauchySeriesWithBound
  B terms =
    Σ[ absolute ∈
      IsAbsolutelyCauchySeries terms ]
      AbsoluteCauchySeriesSumBound
        B terms absolute

opaque
  absoluteMertensCauchyProductWithBound :
    ∀ (A B : ℚ₊)
      (a b : RealSequence) →
    AbsoluteCauchySeriesWithBound A a →
    AbsoluteCauchySeriesWithBound B b →
    AbsoluteCauchySeriesWithBound
      (A ·₊ B)
      (cauchyProduct a b)
  absoluteMertensCauchyProductWithBound
    A B a b
    (a-absolute , a-sum-bounded)
    (b-absolute , b-sum-bounded) =
      product-absolute
      ,
      absoluteMertensCauchyProductAbsoluteSumBound
        A B a b
        a-absolute b-absolute
        a-sum-bounded b-sum-bounded
        product-absolute
    where
    product-absolute :
      IsAbsolutelyCauchySeries
        (cauchyProduct a b)
    product-absolute =
      absoluteMertensCauchyProductIsAbsolutelyCauchy
        A B a b
        a-absolute b-absolute
        a-sum-bounded b-sum-bounded
