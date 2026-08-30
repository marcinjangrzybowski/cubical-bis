module Cubical.Analysis.Real.Series.FiniteModification where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat as ℕ using (ℕ)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Tails

open import Cubical.Relation.Premetric.Properties


private
  module ℝTheory = PremetricTheory ℝPremetricSpace

  correctionReorder : ∀ a b tail →
    (a + tail) + (b - a) ≡
    b + tail
  correctionReorder a b tail =
    cong ((a + tail) +_)
      (addComm b (- a))
    ∙ addAssoc (a + tail) (- a) b
    ∙ cong (_+ b)
        ( cong (_+ (- a)) (addComm a tail)
        ∙ sym (addAssoc tail a (- a))
        ∙ cong (tail +_) (addInvR a)
        ∙ addIdR tail
        )
    ∙ addComm tail b

  eventuallyEqualSeqWitness : ∀ a b →
    ℝTheory.EventuallyEqualSeq a b →
    SeqWitness a → SeqWitness b
  eventuallyEqualSeqWitness a b eventual =
    PT.map
      (ℝTheory.eventuallyEqualSeqPresIsCauchySeq
        a b eventual)


-- An explicit cutoff is useful for calculating the finite correction.  Its
-- truncation is the choice-free assertion that two series eventually agree.

EventuallyEqualSeriesTail :
  RealSequence → RealSequence → Type₀
EventuallyEqualSeriesTail a b =
  Σ[ start ∈ ℕ ]
    (∀ n → start ℕ.≤ n → a n ≡ b n)


EventuallyEqualSeries :
  RealSequence → RealSequence → Type₀
EventuallyEqualSeries a b =
  ∥ EventuallyEqualSeriesTail a b ∥₁


isPropEventuallyEqualSeries : ∀ a b →
  isProp (EventuallyEqualSeries a b)
isPropEventuallyEqualSeries a b = squash₁


eventuallyEqualTailRefl : ∀ a →
  EventuallyEqualSeriesTail a a
eventuallyEqualTailRefl a =
  0 , λ _ _ → refl


eventuallyEqualTailSym : ∀ {a b} →
  EventuallyEqualSeriesTail a b →
  EventuallyEqualSeriesTail b a
eventuallyEqualTailSym (start , equal) =
  start , λ n start≤n → sym (equal n start≤n)


eventuallyEqualTailTrans : ∀ {a b c} →
  EventuallyEqualSeriesTail a b →
  EventuallyEqualSeriesTail b c →
  EventuallyEqualSeriesTail a c
eventuallyEqualTailTrans (K , left) (L , right) =
  ℕ.max K L , λ n max≤n →
    left n
      (ℕ.≤-trans
        (ℕ.left-≤-max {m = K} {n = L}) max≤n)
    ∙ right n
      (ℕ.≤-trans
        (ℕ.right-≤-max {n = L} {m = K}) max≤n)


eventuallyEqualSeriesRefl : ∀ a →
  EventuallyEqualSeries a a
eventuallyEqualSeriesRefl a =
  ∣ eventuallyEqualTailRefl a ∣₁


eventuallyEqualSeriesSym : ∀ {a b} →
  EventuallyEqualSeries a b →
  EventuallyEqualSeries b a
eventuallyEqualSeriesSym =
  PT.map eventuallyEqualTailSym


eventuallyEqualSeriesTrans : ∀ {a b c} →
  EventuallyEqualSeries a b →
  EventuallyEqualSeries b c →
  EventuallyEqualSeries a c
eventuallyEqualSeriesTrans =
  PT.map2 eventuallyEqualTailTrans


private
  correctedPartialSumsEventuallyEqual : ∀ {a b} →
    (eventual : EventuallyEqualSeriesTail a b) →
    ℝTheory.EventuallyEqualSeq
      (λ n →
        partialSum a n
          + (partialSum b (fst eventual)
            - partialSum a (fst eventual)))
      (partialSum b)
  correctedPartialSumsEventuallyEqual
      {a} {b} (start , equal) =
    start
    , λ n start≤n →
        let
          count : ℕ
          count = n ℕ.∸ start

          count+start≡n : count ℕ.+ start ≡ n
          count+start≡n = ℕ.≤-∸-+-cancel start≤n

          tailsPointwise : ∀ k →
            dropSeries start a k ≡
            dropSeries start b k
          tailsPointwise k =
            equal (k ℕ.+ start) ℕ.≤SumRight

          tailPartialSumsEqual : ∀ k →
            partialSum (dropSeries start a) k ≡
            partialSum (dropSeries start b) k
          tailPartialSumsEqual =
            partialSum-pointwise
              (dropSeries start a)
              (dropSeries start b)
              tailsPointwise

          aAtN :
            partialSum a n ≡
            partialSum a start
              + partialSum (dropSeries start a) count
          aAtN =
            cong (partialSum a) (sym count+start≡n)
            ∙ partialSum-drop-recombine start a count

          bAtN :
            partialSum b n ≡
            partialSum b start
              + partialSum (dropSeries start b) count
          bAtN =
            cong (partialSum b) (sym count+start≡n)
            ∙ partialSum-drop-recombine start b count
        in
        cong
          (_+ (partialSum b start - partialSum a start))
          aAtN
        ∙ cong
            (λ tail →
              (partialSum a start + tail)
                + (partialSum b start - partialSum a start))
            (tailPartialSumsEqual count)
        ∙ correctionReorder
            (partialSum a start)
            (partialSum b start)
            (partialSum (dropSeries start b) count)
        ∙ sym bAtN


-- The Cauchy proof transforms the existing `SeqWitness`; it does not infer
-- one from a limit.  This keeps the completion's global-modulus distinction
-- explicit.

eventuallyEqualTailSeriesPresIsCauchy : ∀ {a b} →
  EventuallyEqualSeriesTail a b →
  IsCauchySeries a → IsCauchySeries b
eventuallyEqualTailSeriesPresIsCauchy
    {a} {b} (start , equal) a-cauchy =
  eventuallyEqualSeqWitness
    correctedPartialSums
    (partialSum b)
    correctedEqualsModified
    correctedPartialSumsCauchy
  where
  correction : ℝ
  correction =
    partialSum b start - partialSum a start

  correctedPartialSums : RealSequence
  correctedPartialSums n =
    partialSum a n + correction

  correctedPartialSumsCauchy :
    SeqWitness correctedPartialSums
  correctedPartialSumsCauchy =
    addSeqWitness a-cauchy
      (constantSeqWitness correction)

  correctedEqualsModified :
    ℝTheory.EventuallyEqualSeq
      correctedPartialSums (partialSum b)
  correctedEqualsModified =
    correctedPartialSumsEventuallyEqual
      (start , equal)


eventuallyEqualSeriesPresIsCauchy : ∀ {a b} →
  EventuallyEqualSeries a b →
  IsCauchySeries a → IsCauchySeries b
eventuallyEqualSeriesPresIsCauchy {b = b} eventual a-cauchy =
  PT.rec (isPropIsCauchySeries b)
    (λ tail →
      eventuallyEqualTailSeriesPresIsCauchy
        tail a-cauchy)
    eventual


eventuallyEqualSeriesReflectsIsCauchy : ∀ {a b} →
  EventuallyEqualSeries a b →
  IsCauchySeries b → IsCauchySeries a
eventuallyEqualSeriesReflectsIsCauchy eventual =
  eventuallyEqualSeriesPresIsCauchy
    (eventuallyEqualSeriesSym eventual)


eventuallyEqualTailSeriesHasSum : ∀ {a b} →
  (eventual : EventuallyEqualSeriesTail a b) →
  ∀ value → HasSum a value →
  HasSum b
    ( value
    + (partialSum b (fst eventual)
      - partialSum a (fst eventual))
    )
eventuallyEqualTailSeriesHasSum
    {a} {b} eventual@(start , equal) value a-sum =
  ℝTheory.eventuallyEqualSeqPresIsLimitSeq
    correctedPartialSums
    (partialSum b)
    correctedValue
    correctedEqualsModified
    correctedLimit
  where
  correction : ℝ
  correction =
    partialSum b start - partialSum a start

  correctedValue : ℝ
  correctedValue = value + correction

  correctedPartialSums : RealSequence
  correctedPartialSums n =
    partialSum a n + correction

  correctedLimit :
    isLimitSequence correctedPartialSums correctedValue
  correctedLimit =
    addPresIsLimitSequence
      a-sum (constantIsLimitSequence correction)

  correctedEqualsModified :
    ℝTheory.EventuallyEqualSeq
      correctedPartialSums (partialSum b)
  correctedEqualsModified =
    correctedPartialSumsEventuallyEqual eventual


eventuallyEqualTailSeriesReflectsHasSum : ∀ {a b} →
  (eventual : EventuallyEqualSeriesTail a b) →
  ∀ value → HasSum b value →
  HasSum a
    ( value
    + (partialSum a (fst eventual)
      - partialSum b (fst eventual))
    )
eventuallyEqualTailSeriesReflectsHasSum eventual =
  eventuallyEqualTailSeriesHasSum
    (eventuallyEqualTailSym eventual)


FiniteModificationHasSumWitness : ∀ a b value → Type₀
FiniteModificationHasSumWitness a b value =
  Σ[ eventual ∈ EventuallyEqualSeriesTail a b ]
    HasSum b
      ( value
      + (partialSum b (fst eventual)
        - partialSum a (fst eventual))
      )


eventuallyEqualSeriesHasSum : ∀ {a b} →
  EventuallyEqualSeries a b →
  ∀ value → HasSum a value →
  ∥ FiniteModificationHasSumWitness a b value ∥₁
eventuallyEqualSeriesHasSum eventual value a-sum =
  PT.map
    (λ tail →
      tail
      , eventuallyEqualTailSeriesHasSum
          tail value a-sum)
    eventual


FiniteModificationReflectedHasSumWitness :
  ∀ a b value → Type₀
FiniteModificationReflectedHasSumWitness a b value =
  Σ[ eventual ∈ EventuallyEqualSeriesTail a b ]
    HasSum a
      ( value
      + (partialSum a (fst eventual)
        - partialSum b (fst eventual))
      )


eventuallyEqualSeriesReflectsHasSum : ∀ {a b} →
  EventuallyEqualSeries a b →
  ∀ value → HasSum b value →
  ∥ FiniteModificationReflectedHasSumWitness
      a b value ∥₁
eventuallyEqualSeriesReflectsHasSum eventual value b-sum =
  PT.map
    (λ tail →
      tail
      , eventuallyEqualTailSeriesReflectsHasSum
          tail value b-sum)
    eventual


eventuallyEqualTailSeriesPresSummable : ∀ {a b} →
  EventuallyEqualSeriesTail a b →
  Summable a → Summable b
eventuallyEqualTailSeriesPresSummable
    {a} {b} eventual a-summable =
  seriesSum a a-summable
    + (partialSum b (fst eventual)
      - partialSum a (fst eventual))
  , eventuallyEqualTailSeriesHasSum
      eventual
      (seriesSum a a-summable)
      (seriesSumHasSum a a-summable)


eventuallyEqualSeriesPresSummable : ∀ {a b} →
  EventuallyEqualSeries a b →
  Summable a → Summable b
eventuallyEqualSeriesPresSummable {b = b} eventual a-summable =
  PT.rec (isPropSummable b)
    (λ tail →
      eventuallyEqualTailSeriesPresSummable
        tail a-summable)
    eventual


eventuallyEqualSeriesReflectsSummable : ∀ {a b} →
  EventuallyEqualSeries a b →
  Summable b → Summable a
eventuallyEqualSeriesReflectsSummable eventual =
  eventuallyEqualSeriesPresSummable
    (eventuallyEqualSeriesSym eventual)


seriesSum-finiteModificationAt : ∀ {a b} →
  (eventual : EventuallyEqualSeriesTail a b) →
  (a-summable : Summable a) →
  (b-summable : Summable b) →
  seriesSum b b-summable ≡
  seriesSum a a-summable
    + (partialSum b (fst eventual)
      - partialSum a (fst eventual))
seriesSum-finiteModificationAt
    {a} {b} eventual a-summable b-summable =
  seriesSumIndependent b b-summable
    (eventuallyEqualTailSeriesPresSummable
      eventual a-summable)


FiniteModificationSumWitness : ∀ a b →
  Summable a → Summable b → Type₀
FiniteModificationSumWitness a b a-summable b-summable =
  Σ[ eventual ∈ EventuallyEqualSeriesTail a b ]
    ( seriesSum b b-summable ≡
      seriesSum a a-summable
        + (partialSum b (fst eventual)
          - partialSum a (fst eventual))
    )


seriesSum-finiteModification : ∀ {a b} →
  EventuallyEqualSeries a b →
  (a-summable : Summable a) →
  (b-summable : Summable b) →
  ∥ FiniteModificationSumWitness
      a b a-summable b-summable ∥₁
seriesSum-finiteModification eventual a-summable b-summable =
  PT.map
    (λ tail →
      tail
      , seriesSum-finiteModificationAt
          tail a-summable b-summable)
    eventual
