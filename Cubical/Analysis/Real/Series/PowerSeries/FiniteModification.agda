module Cubical.Analysis.Real.Series.PowerSeries.FiniteModification where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Sequence.Eventually
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.FiniteModification
open import Cubical.Analysis.Real.Series.PowerSeries.Base


coefficientTailToPowerSeriesTail : ∀ {a b} x →
  EventuallyEqualTail a b →
  EventuallyEqualSeriesTail
    (powerSeriesTerms a x) (powerSeriesTerms b x)
coefficientTailToPowerSeriesTail x (start , equal) =
  start
  , λ n start≤n →
      cong (λ coefficient → coefficient · powℝ x n)
        (equal n start≤n)


eventuallyEqualCoefficientsPresPowerSeriesTerms : ∀ {a b} x →
  EventuallyEqualSequence a b →
  EventuallyEqualSeries
    (powerSeriesTerms a x) (powerSeriesTerms b x)
eventuallyEqualCoefficientsPresPowerSeriesTerms x =
  PT.map (coefficientTailToPowerSeriesTail x)


eventuallyEqualCoefficientsPresPowerSeriesCauchy : ∀ {a b} x →
  EventuallyEqualSequence a b →
  IsCauchySeries (powerSeriesTerms a x) →
  IsCauchySeries (powerSeriesTerms b x)
eventuallyEqualCoefficientsPresPowerSeriesCauchy x eventual =
  eventuallyEqualSeriesPresIsCauchy
    (eventuallyEqualCoefficientsPresPowerSeriesTerms x eventual)


eventuallyEqualCoefficientsReflectsPowerSeriesCauchy : ∀ {a b} x →
  EventuallyEqualSequence a b →
  IsCauchySeries (powerSeriesTerms b x) →
  IsCauchySeries (powerSeriesTerms a x)
eventuallyEqualCoefficientsReflectsPowerSeriesCauchy x eventual =
  eventuallyEqualSeriesReflectsIsCauchy
    (eventuallyEqualCoefficientsPresPowerSeriesTerms x eventual)


eventuallyEqualCoefficientsPresPowerSeriesSummable : ∀ {a b} x →
  EventuallyEqualSequence a b →
  PowerSeriesSummableAt a x →
  PowerSeriesSummableAt b x
eventuallyEqualCoefficientsPresPowerSeriesSummable x eventual =
  eventuallyEqualSeriesPresSummable
    (eventuallyEqualCoefficientsPresPowerSeriesTerms x eventual)


eventuallyEqualCoefficientsReflectsPowerSeriesSummable : ∀ {a b} x →
  EventuallyEqualSequence a b →
  PowerSeriesSummableAt b x →
  PowerSeriesSummableAt a x
eventuallyEqualCoefficientsReflectsPowerSeriesSummable x eventual =
  eventuallyEqualSeriesReflectsSummable
    (eventuallyEqualCoefficientsPresPowerSeriesTerms x eventual)


powerSeriesHasSum-finiteModificationAt : ∀ {a b} x →
  (eventual : EventuallyEqualTail a b) →
  ∀ value →
  HasSum (powerSeriesTerms a x) value →
  HasSum (powerSeriesTerms b x)
    ( value
    + ( partialSum (powerSeriesTerms b x) (fst eventual)
      - partialSum (powerSeriesTerms a x) (fst eventual)
      )
    )
powerSeriesHasSum-finiteModificationAt
    x eventual value aHasSum =
  eventuallyEqualTailSeriesHasSum
    (coefficientTailToPowerSeriesTail x eventual)
    value aHasSum


powerSeriesHasSum-reflectsFiniteModificationAt : ∀ {a b} x →
  (eventual : EventuallyEqualTail a b) →
  ∀ value →
  HasSum (powerSeriesTerms b x) value →
  HasSum (powerSeriesTerms a x)
    ( value
    + ( partialSum (powerSeriesTerms a x) (fst eventual)
      - partialSum (powerSeriesTerms b x) (fst eventual)
      )
    )
powerSeriesHasSum-reflectsFiniteModificationAt
    x eventual value bHasSum =
  eventuallyEqualTailSeriesReflectsHasSum
    (coefficientTailToPowerSeriesTail x eventual)
    value bHasSum


powerSeriesValue-finiteModificationAt : ∀ {a b} x →
  (eventual : EventuallyEqualTail a b) →
  (aSummable : PowerSeriesSummableAt a x) →
  (bSummable : PowerSeriesSummableAt b x) →
  powerSeriesValue b x bSummable ≡
  powerSeriesValue a x aSummable
    + ( partialSum (powerSeriesTerms b x) (fst eventual)
      - partialSum (powerSeriesTerms a x) (fst eventual)
      )
powerSeriesValue-finiteModificationAt
    x eventual aSummable bSummable =
  seriesSum-finiteModificationAt
    (coefficientTailToPowerSeriesTail x eventual)
    aSummable bSummable


powerSeriesValue-reflectsFiniteModificationAt : ∀ {a b} x →
  (eventual : EventuallyEqualTail a b) →
  (aSummable : PowerSeriesSummableAt a x) →
  (bSummable : PowerSeriesSummableAt b x) →
  powerSeriesValue a x aSummable ≡
  powerSeriesValue b x bSummable
    + ( partialSum (powerSeriesTerms a x) (fst eventual)
      - partialSum (powerSeriesTerms b x) (fst eventual)
      )
powerSeriesValue-reflectsFiniteModificationAt
    x eventual aSummable bSummable =
  seriesSum-finiteModificationAt
    (eventuallyEqualTailSym
      (coefficientTailToPowerSeriesTail x eventual))
    bSummable aSummable


PowerSeriesFiniteModificationValueWitness :
  ∀ a b x →
  PowerSeriesSummableAt a x →
  PowerSeriesSummableAt b x → Type₀
PowerSeriesFiniteModificationValueWitness
    a b x aSummable bSummable =
  Σ[ eventual ∈ EventuallyEqualTail a b ]
    ( powerSeriesValue b x bSummable ≡
      powerSeriesValue a x aSummable
        + ( partialSum (powerSeriesTerms b x) (fst eventual)
          - partialSum (powerSeriesTerms a x) (fst eventual)
          )
    )


-- Mere eventual equality transports summability directly.  Its
-- cutoff-dependent numerical correction remains under truncation.

powerSeriesValue-finiteModification : ∀ {a b} x →
  EventuallyEqualSequence a b →
  (aSummable : PowerSeriesSummableAt a x) →
  (bSummable : PowerSeriesSummableAt b x) →
  ∥ PowerSeriesFiniteModificationValueWitness
      a b x aSummable bSummable ∥₁
powerSeriesValue-finiteModification
    x eventual aSummable bSummable =
  PT.map
    (λ tail →
      tail
      , powerSeriesValue-finiteModificationAt
          x tail aSummable bSummable)
    eventual
