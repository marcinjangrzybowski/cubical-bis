module Cubical.Analysis.Real.Series.PowerSeries.Product.Convergence where

open import Cubical.Foundations.Prelude

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Absolute
open import Cubical.Analysis.Real.Series.Product.Finite
open import Cubical.Analysis.Real.Series.Product.Convergence
open import Cubical.Analysis.Real.Series.PowerSeries.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Product


powerSeriesCauchyProductHasSum :
  ∀ A B (a b : RealSequence) (x aSum bSum : ℝ) →
  UniformAbsolutePartialSumBound A (powerSeriesTerms a x) →
  UniformPartialSumAbsBound B (powerSeriesTerms b x) →
  IsAbsolutelyCauchySeries (powerSeriesTerms a x) →
  IsCauchySeries (powerSeriesTerms b x) →
  HasSum (powerSeriesTerms a x) aSum →
  HasSum (powerSeriesTerms b x) bSum →
  HasSum
    (powerSeriesTerms (cauchyProduct a b) x)
    (aSum · bSum)
powerSeriesCauchyProductHasSum
  A B a b x aSum bSum
  a-absolute-bounded b-bounded
  a-absolute-cauchy b-cauchy a-has-sum b-has-sum =
    subst
      (λ terms → HasSum terms (aSum · bSum))
      (sym (powerSeriesTerms-cauchyProduct-sequence a b x))
      (mertensCauchyProductHasSum
        A B
        (powerSeriesTerms a x) (powerSeriesTerms b x)
        aSum bSum
        a-absolute-bounded b-bounded
        a-absolute-cauchy b-cauchy a-has-sum b-has-sum)


powerSeriesCauchyProductSummable :
  ∀ A B (a b : RealSequence) (x : ℝ) →
  UniformAbsolutePartialSumBound A (powerSeriesTerms a x) →
  UniformPartialSumAbsBound B (powerSeriesTerms b x) →
  IsAbsolutelyCauchySeries (powerSeriesTerms a x) →
  IsCauchySeries (powerSeriesTerms b x) →
  PowerSeriesSummableAt (cauchyProduct a b) x
powerSeriesCauchyProductSummable
  A B a b x
  a-absolute-bounded b-bounded
  a-absolute-cauchy b-cauchy =
    subst Summable
      (sym (powerSeriesTerms-cauchyProduct-sequence a b x))
      (mertensCauchyProductSummable
        A B
        (powerSeriesTerms a x) (powerSeriesTerms b x)
        a-absolute-bounded b-bounded
        a-absolute-cauchy b-cauchy)
