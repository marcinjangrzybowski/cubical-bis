module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.Equivalence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Sequence
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Surjectivity
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.Limit


opaque
  sineQuarterApproximateIntermediateValue→intermediateValue :
    ∀ quarter →
    SineQuarterApproximateIntermediateValue quarter →
    SineQuarterIntermediateValue quarter
  sineQuarterApproximateIntermediateValue→intermediateValue
      quarter approximate target lower upper =
    PT.map
      (sineQuarterApproximation→preimage quarter target)
      (approximate target lower upper)


  sineQuarterIntermediateValue→approximateIntermediateValue :
    ∀ quarter →
    SineQuarterIntermediateValue quarter →
    SineQuarterApproximateIntermediateValue quarter
  sineQuarterIntermediateValue→approximateIntermediateValue
      quarter intermediate target lower upper =
    PT.map constant-approximation
      (intermediate target lower upper)
    where
    constant-approximation :
      Σ[ point ∈ SineQuarterInterval quarter ]
        sinℝ (fst point) ≡ target →
      SineQuarterApproximation quarter target
    constant-approximation (point , sine-value) =
      (λ _ → point)
      , constantSeqWitness (fst point)
      , subst
          (λ value →
            isLimitSequence (λ _ → sinℝ (fst point)) value)
          sine-value
          (constantIsLimitSequence (sinℝ (fst point)))


sineQuarterApproximateIntermediateValue≃IntermediateValue :
  ∀ quarter →
  SineQuarterApproximateIntermediateValue quarter
    ≃ SineQuarterIntermediateValue quarter
sineQuarterApproximateIntermediateValue≃IntermediateValue quarter =
  propBiimpl→Equiv
    (isPropSineQuarterApproximateIntermediateValue quarter)
    (isPropSineQuarterIntermediateValue quarter)
    (sineQuarterApproximateIntermediateValue→intermediateValue quarter)
    (sineQuarterIntermediateValue→approximateIntermediateValue quarter)
