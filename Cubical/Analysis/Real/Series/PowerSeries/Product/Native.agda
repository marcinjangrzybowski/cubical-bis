module Cubical.Analysis.Real.Series.PowerSeries.Product.Native where

open import Cubical.Foundations.Prelude

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Absolute
open import Cubical.Analysis.Real.Series.Product.Finite
open import Cubical.Analysis.Real.Series.Product.Native
open import Cubical.Analysis.Real.Series.PowerSeries.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Product


-- Native Cauchy hypotheses already contain merely existing rational bounds.
-- The series-level Mertens theorem eliminates those bounds propositionally,
-- so the power-series bridge needs no additional selected constants.

powerSeriesNativeCauchyProductHasSum :
  ∀ (a b : RealSequence) (x aSum bSum : ℝ) →
  IsAbsolutelyCauchySeries (powerSeriesTerms a x) →
  IsCauchySeries (powerSeriesTerms b x) →
  HasSum (powerSeriesTerms a x) aSum →
  HasSum (powerSeriesTerms b x) bSum →
  HasSum
    (powerSeriesTerms (cauchyProduct a b) x)
    (aSum · bSum)
powerSeriesNativeCauchyProductHasSum
    a b x aSum bSum
    a-absolute-cauchy b-cauchy a-has-sum b-has-sum =
  subst
    (λ terms → HasSum terms (aSum · bSum))
    (sym (powerSeriesTerms-cauchyProduct-sequence a b x))
    (nativeMertensCauchyProductHasSum
      (powerSeriesTerms a x) (powerSeriesTerms b x)
      aSum bSum
      a-absolute-cauchy b-cauchy a-has-sum b-has-sum)


powerSeriesNativeCauchyProductSummable :
  ∀ (a b : RealSequence) (x : ℝ) →
  IsAbsolutelyCauchySeries (powerSeriesTerms a x) →
  IsCauchySeries (powerSeriesTerms b x) →
  PowerSeriesSummableAt (cauchyProduct a b) x
powerSeriesNativeCauchyProductSummable
    a b x a-absolute-cauchy b-cauchy =
  subst Summable
    (sym (powerSeriesTerms-cauchyProduct-sequence a b x))
    (nativeMertensCauchyProductSummable
      (powerSeriesTerms a x) (powerSeriesTerms b x)
      a-absolute-cauchy b-cauchy)
