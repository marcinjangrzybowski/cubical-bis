module Cubical.Analysis.Real.Series.Absolute where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Metric.AbsoluteDifference
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Sequence.Eventually
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Bounds


absolutePartialSum : RealSequence → RealSequence
absolutePartialSum terms =
  partialSum (absℝ ∘ terms)


IsAbsolutelyCauchySeries : RealSequence → Type₀
IsAbsolutelyCauchySeries terms =
  IsCauchySeries (absℝ ∘ terms)


isPropIsAbsolutelyCauchySeries : ∀ terms →
  isProp (IsAbsolutelyCauchySeries terms)
isPropIsAbsolutelyCauchySeries terms = squash₁


AbsolutelySummable : RealSequence → Type₀
AbsolutelySummable terms =
  Summable (absℝ ∘ terms)


isPropAbsolutelySummable : ∀ terms →
  isProp (AbsolutelySummable terms)
isPropAbsolutelySummable terms =
  isPropSummable (absℝ ∘ terms)


-- This comparison deliberately consumes the native Cauchy witness of the
-- dominating series.  Mere convergence does not choose the global modulus
-- required by the sequential-completion constructor.
dominatedChosenCauchySeriesIsChosenCauchy :
  (terms bound : RealSequence) →
  (∀ n → absℝ (terms n) ≤ℝ bound n) →
  ChosenIsCauchySequence (partialSum bound) →
  ChosenIsCauchySequence (partialSum terms)
dominatedChosenCauchySeriesIsChosenCauchy
    terms bound dominates bound-cauchy .fst =
  fst bound-cauchy
dominatedChosenCauchySeriesIsChosenCauchy
    terms bound dominates bound-cauchy .snd
    ε m n modulus≤m modulus≤n =
  absDifference<→closeness
    (partialSum terms m) (partialSum terms n) ε
    (≤<ℝ-trans
      (absℝ (partialSum terms m - partialSum terms n))
      (absℝ (partialSum bound m - partialSum bound n))
      (rat (fst ε))
      (partialSumDistanceBoundBy
        terms bound dominates m n)
      (closeness→absDifference<
        (partialSum bound m) (partialSum bound n) ε
        (snd bound-cauchy ε m n modulus≤m modulus≤n)))


dominatedCauchySeriesIsCauchy :
  (terms bound : RealSequence) →
  (∀ n → absℝ (terms n) ≤ℝ bound n) →
  IsCauchySeries bound →
  IsCauchySeries terms
dominatedCauchySeriesIsCauchy terms bound dominates =
  PT.map
    (dominatedChosenCauchySeriesIsChosenCauchy
      terms bound dominates)


dominatedCauchySeriesIsSummable :
  (terms bound : RealSequence) →
  (∀ n → absℝ (terms n) ≤ℝ bound n) →
  IsCauchySeries bound →
  Summable terms
dominatedCauchySeriesIsSummable terms bound dominates bound-cauchy =
  cauchySeriesIsSummable terms
    (dominatedCauchySeriesIsCauchy
      terms bound dominates bound-cauchy)


absoluteCauchySeriesIsCauchy :
  (terms : RealSequence) →
  IsAbsolutelyCauchySeries terms →
  IsCauchySeries terms
absoluteCauchySeriesIsCauchy terms =
  dominatedCauchySeriesIsCauchy
    terms (absℝ ∘ terms)
    (λ n → ≤ℝ-refl (absℝ (terms n)))


absoluteCauchySeriesIsSummable :
  (terms : RealSequence) →
  IsAbsolutelyCauchySeries terms →
  Summable terms
absoluteCauchySeriesIsSummable terms absolute =
  cauchySeriesIsSummable terms
    (absoluteCauchySeriesIsCauchy terms absolute)


absoluteCauchySeriesIsAbsolutelySummable :
  (terms : RealSequence) →
  IsAbsolutelyCauchySeries terms →
  AbsolutelySummable terms
absoluteCauchySeriesIsAbsolutelySummable terms =
  cauchySeriesIsSummable (absℝ ∘ terms)


seriesSumAbsBound :
  (terms : RealSequence) →
  (summable : Summable terms) →
  (absolute-summable : AbsolutelySummable terms) →
  absℝ (seriesSum terms summable) ≤ℝ
  seriesSum (absℝ ∘ terms) absolute-summable
seriesSumAbsBound terms summable absolute-summable =
  pointwiseLePresLimits
    (partialSumAbsBound terms)
    (continuousPreservesIsLimitSequence
      absℝ abs-isContinuous
      (seriesSumHasSum terms summable))
    (seriesSumHasSum
      (absℝ ∘ terms) absolute-summable)


absoluteCauchySeriesSumAbsBound :
  (terms : RealSequence) →
  (absolute : IsAbsolutelyCauchySeries terms) →
  absℝ
    (seriesSum terms
      (absoluteCauchySeriesIsSummable terms absolute))
    ≤ℝ
  seriesSum (absℝ ∘ terms)
    (absoluteCauchySeriesIsAbsolutelySummable terms absolute)
absoluteCauchySeriesSumAbsBound terms absolute =
  seriesSumAbsBound
    terms
    (absoluteCauchySeriesIsSummable terms absolute)
    (absoluteCauchySeriesIsAbsolutelySummable terms absolute)
