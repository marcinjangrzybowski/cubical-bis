module Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Product where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat as ℕ
  using (ℕ ; suc ; _∸_)
import Cubical.Data.Nat.Order as ℕ

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
  Cubical.HITs.CauchyRealsP.Analysis.Series.Geometric.Comparison
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Geometric.Convolution
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Base
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.PowerSeries.Convergence

boundedPowerSplit :
  ∀ (x : ℝ) (n k : ℕ) →
  k ℕ.≤ n →
  x ^ⁿ k · x ^ⁿ (n ∸ k)
    ≡
  x ^ⁿ n
boundedPowerSplit x n k k≤n =
  ℝExponentiation.·-of-^-is-^-of-+
    x k (n ∸ k)
  ∙ cong (x ^ⁿ_)
      ( ℕ.+-comm k (n ∸ k)
      ∙ ℕ.≤-∸-+-cancel k≤n
      )

rearrangePowerSeriesTerm :
  ∀ (a b : RealSequence)
    (x : ℝ) (n k : ℕ) →
  k ℕ.≤ n →
  (a k · b (n ∸ k)) · x ^ⁿ n
    ≡
  (a k · x ^ⁿ k)
    · (b (n ∸ k) · x ^ⁿ (n ∸ k))
rearrangePowerSeriesTerm
  a b x n k k≤n =
    cong
      ((a k · b (n ∸ k)) ·_)
      (sym
        (boundedPowerSplit
          x n k k≤n))
  ∙ rearrange
      (a k) (b (n ∸ k))
      (x ^ⁿ k) (x ^ⁿ (n ∸ k))
  where
  rearrange : ∀ (p q r s : ℝ) →
    (p · q) · (r · s) ≡
    (p · r) · (q · s)
  rearrange p q r s =
    mulAssoc p q (r · s)
    ∙ cong (p ·_)
        (sym (mulAssoc q r s))
    ∙ cong
        (λ z → p · (z · s))
        (mulComm q r)
    ∙ cong (p ·_)
        (mulAssoc r q s)
    ∙ sym
        (mulAssoc p r (q · s))

powerSeriesTerms-cauchyProduct :
  ∀ (a b : RealSequence)
    (x : ℝ) (n : ℕ) →
  powerSeriesTerms
      (cauchyProduct a b) x n
    ≡
  cauchyProduct
    (powerSeriesTerms a x)
    (powerSeriesTerms b x)
    n
powerSeriesTerms-cauchyProduct a b x n =
  sym
    (partialSum-right-scale
      (λ k → a k · b (n ∸ k))
      (x ^ⁿ n)
      (suc n))
  ∙ partialSum-pointwiseBefore
      (λ k →
        (a k · b (n ∸ k))
          · x ^ⁿ n)
      (λ k →
        (a k · x ^ⁿ k)
          ·
        ( b (n ∸ k)
          · x ^ⁿ (n ∸ k)
        ))
      (suc n)
      (λ k k<sucn →
        rearrangePowerSeriesTerm
          a b x n k
          (ℕ.pred-≤-pred k<sucn))

powerSeriesTerms-cauchyProduct-sequence :
  ∀ (a b : RealSequence)
    (x : ℝ) →
  powerSeriesTerms
      (cauchyProduct a b) x
    ≡
  cauchyProduct
    (powerSeriesTerms a x)
    (powerSeriesTerms b x)
powerSeriesTerms-cauchyProduct-sequence
  a b x =
    funExt
      (powerSeriesTerms-cauchyProduct
        a b x)

powerSeriesProductRectangularApproximation :
  ∀ C D (a b : RealSequence) (x : ℝ) →
  CoefficientAbsBound C a →
  CoefficientAbsBound D b →
  (contraction :
    RationalContractionBound x) →
  CauchyProductRectangularApproximation
    (powerSeriesTerms a x)
    (powerSeriesTerms b x)
powerSeriesProductRectangularApproximation
  C D a b x
  a-bounded b-bounded
  contraction@(q , absx<q , q<1) =
    mertensRectangularApproximation
      a-total-bound
      b-total-bound
      (powerSeriesTerms a x)
      (powerSeriesTerms b x)
      a-uniform-absolute-bound
      (uniformAbsoluteBound→uniformBound
        b-total-bound
        (powerSeriesTerms b x)
        b-uniform-absolute-bound)
      a-absolute
      (absoluteCauchySeriesIsCauchy
        (powerSeriesTerms b x)
        b-absolute)
  where
  a-absolute :
    IsAbsolutelyCauchySeries
      (powerSeriesTerms a x)
  a-absolute =
    powerSeriesIsAbsolutelyCauchy
      C a x a-bounded contraction

  b-absolute :
    IsAbsolutelyCauchySeries
      (powerSeriesTerms b x)
  b-absolute =
    powerSeriesIsAbsolutelyCauchy
      D b x b-bounded contraction

  a-total-bound : ℚ₊
  a-total-bound =
    C ·₊ rationalGeometricSumBound q q<1

  b-total-bound : ℚ₊
  b-total-bound =
    D ·₊ rationalGeometricSumBound q q<1

  absx≤q :
    absℝ x ≤ℝ rat (fst q)
  absx≤q =
    <ℝ-weaken
      (absℝ x)
      (rat (fst q))
      absx<q

  a-uniform-absolute-bound :
    UniformAbsolutePartialSumBound
      a-total-bound
      (powerSeriesTerms a x)
  a-uniform-absolute-bound =
    absoluteCauchySumBound→uniformAbsoluteBound
      a-total-bound
      (powerSeriesTerms a x)
      a-absolute
      (powerSeriesAbsoluteSumBoundByMajorant
        C q a x
        a-bounded absx≤q q<1
        a-absolute)

  b-uniform-absolute-bound :
    UniformAbsolutePartialSumBound
      b-total-bound
      (powerSeriesTerms b x)
  b-uniform-absolute-bound =
    absoluteCauchySumBound→uniformAbsoluteBound
      b-total-bound
      (powerSeriesTerms b x)
      b-absolute
      (powerSeriesAbsoluteSumBoundByMajorant
        D q b x
        b-bounded absx≤q q<1
        b-absolute)

powerSeriesCauchyProductSummable :
  ∀ C D (a b : RealSequence) (x : ℝ) →
  CoefficientAbsBound C a →
  CoefficientAbsBound D b →
  (contraction :
    RationalContractionBound x) →
  PowerSeriesSummableAt
    (cauchyProduct a b) x
powerSeriesCauchyProductSummable
  C D a b x
  a-bounded b-bounded contraction =
    subst Summable
      (sym
        (powerSeriesTerms-cauchyProduct-sequence
          a b x))
      (cauchyProductSummable
        (powerSeriesTerms a x)
        (powerSeriesTerms b x)
        a-summable b-summable
        (powerSeriesProductRectangularApproximation
          C D a b x
          a-bounded b-bounded contraction))
  where
  a-summable :
    PowerSeriesSummableAt a x
  a-summable =
    powerSeriesIsSummable
      C a x a-bounded contraction

  b-summable :
    PowerSeriesSummableAt b x
  b-summable =
    powerSeriesIsSummable
      D b x b-bounded contraction

powerSeriesValue-cauchyProduct :
  ∀ C D (a b : RealSequence) (x : ℝ) →
  CoefficientAbsBound C a →
  CoefficientAbsBound D b →
  (contraction :
    RationalContractionBound x) →
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
powerSeriesValue-cauchyProduct
  C D a b x
  a-bounded b-bounded contraction
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

  coefficient-product-terms : RealSequence
  coefficient-product-terms =
    powerSeriesTerms
      (cauchyProduct a b) x

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
      (powerSeriesProductRectangularApproximation
        C D a b x
        a-bounded b-bounded contraction)

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
