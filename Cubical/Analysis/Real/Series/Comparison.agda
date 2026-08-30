module Cubical.Analysis.Real.Series.Comparison where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Sequence.Eventually
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Bounds


seriesSumMono : ∀ a b →
  (a-summable : Summable a) →
  (b-summable : Summable b) →
  (∀ n → a n ≤ℝ b n) →
  seriesSum a a-summable ≤ℝ seriesSum b b-summable
seriesSumMono a b a-summable b-summable pointwise =
  pointwiseLePresLimits
    (partialSumMono a b pointwise)
    (seriesSumHasSum a a-summable)
    (seriesSumHasSum b b-summable)


seriesSumNonnegative : ∀ terms →
  (summable : Summable terms) →
  (∀ n → 0ℝ ≤ℝ terms n) →
  0ℝ ≤ℝ seriesSum terms summable
seriesSumNonnegative terms summable nonnegative =
  pointwiseLePresLimits
    (partialSumNonnegative terms nonnegative)
    (constantIsLimitSequence 0ℝ)
    (seriesSumHasSum terms summable)


seriesSumUpperBound : ∀ terms →
  (summable : Summable terms) →
  (bound : ℝ) →
  (∀ n → partialSum terms n ≤ℝ bound) →
  seriesSum terms summable ≤ℝ bound
seriesSumUpperBound terms summable bound bounded =
  pointwiseLePresLimits bounded
    (seriesSumHasSum terms summable)
    (constantIsLimitSequence bound)


seriesSumLowerBound : ∀ terms →
  (summable : Summable terms) →
  (bound : ℝ) →
  (∀ n → bound ≤ℝ partialSum terms n) →
  bound ≤ℝ seriesSum terms summable
seriesSumLowerBound terms summable bound bounded =
  pointwiseLePresLimits bounded
    (constantIsLimitSequence bound)
    (seriesSumHasSum terms summable)


-- Comparison with an arbitrary summable majorant.  Unlike the native-Cauchy
-- comparison, this conclusion only concerns the value and therefore needs no
-- selected global modulus.
seriesSumAbsBoundBy : ∀ terms bound →
  (terms-summable : Summable terms) →
  (bound-summable : Summable bound) →
  (∀ n → absℝ (terms n) ≤ℝ bound n) →
  absℝ (seriesSum terms terms-summable) ≤ℝ
  seriesSum bound bound-summable
seriesSumAbsBoundBy terms bound
    terms-summable bound-summable dominates =
  pointwiseLePresLimits partial-bounds
    (continuousPreservesIsLimitSequence
      absℝ abs-isContinuous
      (seriesSumHasSum terms terms-summable))
    (seriesSumHasSum bound bound-summable)
  where
  partial-bounds : ∀ n →
    absℝ (partialSum terms n) ≤ℝ partialSum bound n
  partial-bounds n =
    ≤ℝ-trans
      (absℝ (partialSum terms n))
      (partialSum (absℝ ∘ terms) n)
      (partialSum bound n)
      (partialSumAbsBound terms n)
      (partialSumMono (absℝ ∘ terms) bound dominates n)
