module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.FiniteModification where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat as ℕ using (ℕ)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Associativity
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.GroupLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Sequence
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Operations


private
  correctionReorder : ∀ a b tail →
    (a Add.+ tail) Add.+ (b Group.- a) ≡
    b Add.+ tail
  correctionReorder a b tail =
      cong ((a Add.+ tail) Add.+_)
        (add-comm b (Neg.- a))
    ∙ add-assoc (a Add.+ tail) (Neg.- a) b
    ∙ cong (Add._+ b)
        ( cong (Add._+ (Neg.- a)) (add-comm a tail)
        ∙ sym (add-assoc tail a (Neg.- a))
        ∙ cong (tail Add.+_) (add-inverse-right a)
        ∙ add-zero-right tail
        )
    ∙ add-comm tail b


-- The proof with an explicit cutoff is kept as an internal computational
-- lemma.  Public preservation below accepts only the mere existence of such
-- a cutoff, because both Cauchyness and summability are propositions.

eventuallyEqualTailSeriesPresIsCauchy : ∀ {a b} →
  EventuallyEqualTail a b →
  IsCauchySeries a → IsCauchySeries b
eventuallyEqualTailSeriesPresIsCauchy
    {a} {b} (start , equal) a-cauchy =
  eventuallyEqualPresIsCauchySequence
    corrected-equals-modified corrected-cauchy
  where
  correction : Real.ℝ
  correction =
    partialSum b start Group.- partialSum a start

  correctedPartialSums : RealSequence
  correctedPartialSums n =
    partialSum a n Add.+ correction

  corrected-cauchy : IsCauchySequence correctedPartialSums
  corrected-cauchy =
    addPresIsCauchySequence
      a-cauchy (constantIsCauchySequence correction)

  tails-pointwise : ∀ n →
    dropSeries start a n ≡ dropSeries start b n
  tails-pointwise n =
    equal (n ℕ.+ start) ℕ.≤SumRight

  tail-partial-sums-equal : ∀ n →
    partialSum (dropSeries start a) n ≡
    partialSum (dropSeries start b) n
  tail-partial-sums-equal =
    partialSum-pointwise
      (dropSeries start a) (dropSeries start b)
      tails-pointwise

  corrected-equals-modified :
    EventuallyEqualSequence correctedPartialSums (partialSum b)
  corrected-equals-modified =
    ∣ start , (λ n start≤n →
      let
        count : ℕ
        count = n ℕ.∸ start

        count+start≡n : count ℕ.+ start ≡ n
        count+start≡n = ℕ.≤-∸-+-cancel start≤n

        aAtN :
          partialSum a n ≡
          partialSum a start Add.+
            partialSum (dropSeries start a) count
        aAtN =
          cong (partialSum a) (sym count+start≡n)
          ∙ partialSum-drop-recombine start a count

        bAtN :
          partialSum b n ≡
          partialSum b start Add.+
            partialSum (dropSeries start b) count
        bAtN =
          cong (partialSum b) (sym count+start≡n)
          ∙ partialSum-drop-recombine start b count
      in
        cong (Add._+ correction) aAtN
        ∙ cong
            (λ tail →
              (partialSum a start Add.+ tail) Add.+ correction)
            (tail-partial-sums-equal count)
        ∙ correctionReorder
            (partialSum a start)
            (partialSum b start)
            (partialSum (dropSeries start b) count)
        ∙ sym bAtN) ∣₁


eventuallyEqualSeriesPresIsCauchy : ∀ {a b} →
  EventuallyEqualSequence a b →
  IsCauchySeries a → IsCauchySeries b
eventuallyEqualSeriesPresIsCauchy {a} {b} eventual a-cauchy =
  PT.rec (isPropIsCauchySeries b)
    (λ tail → eventuallyEqualTailSeriesPresIsCauchy tail a-cauchy)
    eventual


-- When a caller deliberately retains a cutoff, the exact finite correction
-- remains available.  This theorem is what is used to recover the familiar
-- calculation rule for a finite modification.

eventuallyEqualTailSeriesHasSum : ∀ {a b} →
  (eventual : EventuallyEqualTail a b) →
  ∀ value → HasSum a value →
  HasSum b
    (value Add.+
      ( partialSum b (fst eventual)
      Group.- partialSum a (fst eventual)
      ))
eventuallyEqualTailSeriesHasSum
    {a} {b} eventual@(start , equal) value a-sum =
  eventuallyEqualPresIsLimitSequence
    corrected-equals-modified corrected-limit
  where
  correction : Real.ℝ
  correction =
    partialSum b start Group.- partialSum a start

  correctedPartialSums : RealSequence
  correctedPartialSums n =
    partialSum a n Add.+ correction

  corrected-limit :
    isLimitSequence correctedPartialSums (value Add.+ correction)
  corrected-limit =
    addPresIsLimitSequence
      a-sum (constantIsLimitSequence correction)

  tails-pointwise : ∀ n →
    dropSeries start a n ≡ dropSeries start b n
  tails-pointwise n =
    equal (n ℕ.+ start) ℕ.≤SumRight

  tail-partial-sums-equal : ∀ n →
    partialSum (dropSeries start a) n ≡
    partialSum (dropSeries start b) n
  tail-partial-sums-equal =
    partialSum-pointwise
      (dropSeries start a) (dropSeries start b)
      tails-pointwise

  corrected-equals-modified :
    EventuallyEqualSequence correctedPartialSums (partialSum b)
  corrected-equals-modified =
    ∣ start , (λ n start≤n →
      let
        count : ℕ
        count = n ℕ.∸ start

        count+start≡n : count ℕ.+ start ≡ n
        count+start≡n = ℕ.≤-∸-+-cancel start≤n

        aAtN :
          partialSum a n ≡
          partialSum a start Add.+
            partialSum (dropSeries start a) count
        aAtN =
          cong (partialSum a) (sym count+start≡n)
          ∙ partialSum-drop-recombine start a count

        bAtN :
          partialSum b n ≡
          partialSum b start Add.+
            partialSum (dropSeries start b) count
        bAtN =
          cong (partialSum b) (sym count+start≡n)
          ∙ partialSum-drop-recombine start b count
      in
        cong (Add._+ correction) aAtN
        ∙ cong
            (λ tail →
              (partialSum a start Add.+ tail) Add.+ correction)
            (tail-partial-sums-equal count)
        ∙ correctionReorder
            (partialSum a start)
            (partialSum b start)
            (partialSum (dropSeries start b) count)
        ∙ sym bAtN) ∣₁


-- Preservation itself needs no chosen cutoff.  Eliminating the truncated
-- witness is sound because `Summable b` is a proposition and already
-- contains its uniquely determined, untruncated sum.

eventuallyEqualSeriesPresSummable : ∀ {a b} →
  EventuallyEqualSequence a b →
  Summable a → Summable b
eventuallyEqualSeriesPresSummable {a} {b} eventual a-summable =
  cauchySeriesIsSummable b
    (eventuallyEqualSeriesPresIsCauchy eventual
      (summableIsCauchySeries a a-summable))


seriesSum-finiteModificationAt : ∀ {a b} →
  (eventual : EventuallyEqualTail a b) →
  (a-summable : Summable a) →
  (b-summable : Summable b) →
  seriesSum b b-summable ≡
  seriesSum a a-summable Add.+
    ( partialSum b (fst eventual)
    Group.- partialSum a (fst eventual)
    )
seriesSum-finiteModificationAt
    {a} {b} eventual a-summable b-summable =
  cong fst
    (isPropSequenceLimit (partialSum b)
      b-summable
      (_ , eventuallyEqualTailSeriesHasSum
        eventual
        (seriesSum a a-summable)
        (seriesSumHasSum a a-summable)))


-- The cutoff-sensitive formula cannot expose an `N` from a merely
-- eventual hypothesis.  Its strongest choice-free public form keeps the
-- cutoff and the corresponding equation under one truncation.

FiniteModificationSumWitness : ∀ a b →
  Summable a → Summable b → Type₀
FiniteModificationSumWitness a b a-summable b-summable =
  Σ[ eventual ∈ EventuallyEqualTail a b ]
    ( seriesSum b b-summable ≡
      seriesSum a a-summable Add.+
        ( partialSum b (fst eventual)
        Group.- partialSum a (fst eventual)
        ))


seriesSum-finiteModification : ∀ {a b} →
  EventuallyEqualSequence a b →
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
