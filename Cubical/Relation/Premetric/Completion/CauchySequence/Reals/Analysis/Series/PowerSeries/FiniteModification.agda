module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.FiniteModification where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Powers
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Sequence
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.FiniteModification
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Base


coefficientTailToPowerSeriesTail : ∀ {a b} x →
  EventuallyEqualTail a b →
  EventuallyEqualTail
    (powerSeriesTerms a x) (powerSeriesTerms b x)
coefficientTailToPowerSeriesTail x (start , equal) =
  start , λ n start≤n →
    cong (Mul._· x ^ⁿ n) (equal n start≤n)


eventuallyEqualCoefficientsPresPowerSeriesTerms : ∀ {a b} x →
  EventuallyEqualSequence a b →
  EventuallyEqualSequence
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


eventuallyEqualCoefficientsPresPowerSeriesSummable : ∀ {a b} x →
  EventuallyEqualSequence a b →
  PowerSeriesSummableAt a x →
  PowerSeriesSummableAt b x
eventuallyEqualCoefficientsPresPowerSeriesSummable x eventual =
  eventuallyEqualSeriesPresSummable
    (eventuallyEqualCoefficientsPresPowerSeriesTerms x eventual)


powerSeriesValue-finiteModificationAt : ∀ {a b} x →
  (eventual : EventuallyEqualTail a b) →
  (a-summable : PowerSeriesSummableAt a x) →
  (b-summable : PowerSeriesSummableAt b x) →
  powerSeriesValue b x b-summable ≡
  powerSeriesValue a x a-summable Add.+
    ( partialSum (powerSeriesTerms b x) (fst eventual)
    Group.- partialSum (powerSeriesTerms a x) (fst eventual))
powerSeriesValue-finiteModificationAt
    x eventual a-summable b-summable =
  seriesSum-finiteModificationAt
    (coefficientTailToPowerSeriesTail x eventual)
    a-summable b-summable


PowerSeriesFiniteModificationValueWitness : ∀ a b x →
  PowerSeriesSummableAt a x →
  PowerSeriesSummableAt b x → Type₀
PowerSeriesFiniteModificationValueWitness
    a b x a-summable b-summable =
  Σ[ eventual ∈ EventuallyEqualTail a b ]
    ( powerSeriesValue b x b-summable ≡
      powerSeriesValue a x a-summable Add.+
        ( partialSum (powerSeriesTerms b x) (fst eventual)
        Group.- partialSum (powerSeriesTerms a x) (fst eventual)))


-- As for ordinary series, mere eventual equality proves summability
-- directly, but its cutoff-dependent correction formula remains truncated.

powerSeriesValue-finiteModification : ∀ {a b} x →
  EventuallyEqualSequence a b →
  (a-summable : PowerSeriesSummableAt a x) →
  (b-summable : PowerSeriesSummableAt b x) →
  ∥ PowerSeriesFiniteModificationValueWitness
      a b x a-summable b-summable ∥₁
powerSeriesValue-finiteModification
    x eventual a-summable b-summable =
  PT.map
    (λ tail →
      tail , powerSeriesValue-finiteModificationAt
        x tail a-summable b-summable)
    eventual
