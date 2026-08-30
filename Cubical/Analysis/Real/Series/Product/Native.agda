module Cubical.Analysis.Real.Series.Product.Native where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open PositiveRationals using (ℚ₊)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Absolute
open import Cubical.Analysis.Real.Series.NativeBounds
open import Cubical.Analysis.Real.Series.Product.Finite
open import Cubical.Analysis.Real.Series.Product.Convergence


-- Native Cauchy witnesses construct merely existing rational bounds.  This
-- eliminator exposes them only while proving a proposition, so it does not
-- turn a truncated witness into a globally selected modulus or bound.

withNativeMertensBounds : ∀ a b →
  IsAbsolutelyCauchySeries a →
  IsCauchySeries b →
  (P : Type₀) → isProp P →
  (∀ A B →
    UniformAbsolutePartialSumBound A a →
    UniformPartialSumAbsBound B b → P) →
  P
withNativeMertensBounds
    a b aAbsoluteCauchy bCauchy P isPropP useBounds =
  PT.rec isPropP withAbsoluteBound
    (mereAbsolutelyCauchySeriesUniformAbsolutePartialSumBound
      a aAbsoluteCauchy)
  where
  withAbsoluteBound :
    Σ[ A ∈ ℚ₊ ] UniformAbsolutePartialSumBound A a → P
  withAbsoluteBound (A , aBounded) =
    PT.rec isPropP
      (λ (B , bBounded) →
        useBounds A B aBounded bBounded)
      (mereCauchySeriesUniformPartialSumAbsBound b bCauchy)


nativeMertensRemainderLimit : ∀ a b →
  IsAbsolutelyCauchySeries a →
  IsCauchySeries b →
  isLimitSequence (cauchyProductRemainder a b) 0ℝ
nativeMertensRemainderLimit a b aAbsoluteCauchy bCauchy =
  withNativeMertensBounds
    a b aAbsoluteCauchy bCauchy
    (isLimitSequence (cauchyProductRemainder a b) 0ℝ)
    (isPropIsLimitSequence (cauchyProductRemainder a b) 0ℝ)
    (λ A B aBounded bBounded →
      mertensRemainderLimit
        A B a b aBounded bBounded
        aAbsoluteCauchy bCauchy)


nativeMertensCauchyProductHasSum : ∀ a b aSum bSum →
  IsAbsolutelyCauchySeries a →
  IsCauchySeries b →
  HasSum a aSum →
  HasSum b bSum →
  HasSum (cauchyProduct a b) (aSum · bSum)
nativeMertensCauchyProductHasSum
    a b aSum bSum
    aAbsoluteCauchy bCauchy aHasSum bHasSum =
  withNativeMertensBounds
    a b aAbsoluteCauchy bCauchy
    (HasSum (cauchyProduct a b) (aSum · bSum))
    (isPropIsLimitSequence
      (partialSum (cauchyProduct a b)) (aSum · bSum))
    (λ A B aBounded bBounded →
      mertensCauchyProductHasSum
        A B a b aSum bSum
        aBounded bBounded
        aAbsoluteCauchy bCauchy aHasSum bHasSum)


nativeMertensCauchyProductSummable : ∀ a b →
  IsAbsolutelyCauchySeries a →
  IsCauchySeries b →
  Summable (cauchyProduct a b)
nativeMertensCauchyProductSummable
    a b aAbsoluteCauchy bCauchy =
  withNativeMertensBounds
    a b aAbsoluteCauchy bCauchy
    (Summable (cauchyProduct a b))
    (isPropSummable (cauchyProduct a b))
    (λ A B aBounded bBounded →
      mertensCauchyProductSummable
        A B a b aBounded bBounded
        aAbsoluteCauchy bCauchy)


nativeMertensSeriesSum-cauchyProduct : ∀ a b →
  (aAbsoluteCauchy : IsAbsolutelyCauchySeries a) →
  (bCauchy : IsCauchySeries b) →
  (productSummable : Summable (cauchyProduct a b)) →
  seriesSum (cauchyProduct a b) productSummable ≡
  seriesSum a
      (absoluteCauchySeriesIsSummable a aAbsoluteCauchy)
    ·
  seriesSum b (cauchySeriesIsSummable b bCauchy)
nativeMertensSeriesSum-cauchyProduct
    a b aAbsoluteCauchy bCauchy productSummable =
  withNativeMertensBounds
    a b aAbsoluteCauchy bCauchy _
    (isSetℝ _ _)
    (λ A B aBounded bBounded →
      mertensSeriesSum-cauchyProduct
        A B a b aBounded bBounded
        aAbsoluteCauchy bCauchy productSummable)


nativeMertensCanonicalSeriesSum-cauchyProduct : ∀ a b →
  (aAbsoluteCauchy : IsAbsolutelyCauchySeries a) →
  (bCauchy : IsCauchySeries b) →
  seriesSum (cauchyProduct a b)
      (nativeMertensCauchyProductSummable
        a b aAbsoluteCauchy bCauchy)
    ≡
  seriesSum a
      (absoluteCauchySeriesIsSummable a aAbsoluteCauchy)
    ·
  seriesSum b (cauchySeriesIsSummable b bCauchy)
nativeMertensCanonicalSeriesSum-cauchyProduct
    a b aAbsoluteCauchy bCauchy =
  nativeMertensSeriesSum-cauchyProduct
    a b aAbsoluteCauchy bCauchy
    (nativeMertensCauchyProductSummable
      a b aAbsoluteCauchy bCauchy)
