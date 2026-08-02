module Cubical.HITs.CauchyRealsP.Analysis.Series.FiniteModification where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat as ℕ using (ℕ ; zero ; suc)
import Cubical.Data.Nat.Order as ℕ

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra
open import Cubical.HITs.CauchyRealsP.Analysis.Sequence
open import
  Cubical.HITs.CauchyRealsP.Analysis.Sequence.Cauchy
open import Cubical.HITs.CauchyRealsP.Analysis.Series.Base
open import
  Cubical.HITs.CauchyRealsP.Analysis.Series.Operations

private
  correctionReorder : ∀ a b tail →
    (a + tail) + (b - a) ≡
    b + tail
  correctionReorder a b tail =
    cong
      ((a + tail) +_)
      (addComm b (- a))
    ∙ addAssoc
        (a + tail) (- a) b
    ∙ cong
        (_+ b)
        ( cong (_+ (- a))
            (addComm a tail)
        ∙ sym
            (addAssoc tail a (- a))
        ∙ cong (tail +_)
            (addInvR a)
        ∙ addIdR tail
        )
    ∙ addComm tail b

eventuallyEqualSeriesPresIsCauchy :
  ∀ a b →
  EventuallyEqualSeq a b →
  IsCauchySeries a →
  IsCauchySeries b
eventuallyEqualSeriesPresIsCauchy
  a b (start , equal) a-cauchy =
    eventuallyEqualSeqPresIsCauchySeq
      correctedPartialSums
      (partialSum b)
      correctedEqualsModified
      correctedPartialSumsCauchy
  where
  correction : ℝ
  correction =
    partialSum b start
      - partialSum a start

  correctedPartialSums : RealSequence
  correctedPartialSums n =
    partialSum a n + correction

  correctedPartialSumsCauchy :
    isCauchySeq correctedPartialSums
  correctedPartialSumsCauchy =
    addPresIsCauchySeq
      (partialSum a)
      (λ _ → correction)
      a-cauchy
      (constantIsCauchySeq correction)

  tailsPointwise : ∀ n →
    dropSeries start a n ≡
    dropSeries start b n
  tailsPointwise n =
    equal (n ℕ.+ start) ℕ.≤SumRight

  tailPartialSumsEqual : ∀ n →
    partialSum (dropSeries start a) n ≡
    partialSum (dropSeries start b) n
  tailPartialSumsEqual =
    partialSum-pointwise
      (dropSeries start a)
      (dropSeries start b)
      tailsPointwise

  correctedEqualsModified :
    EventuallyEqualSeq
      correctedPartialSums
      (partialSum b)
  correctedEqualsModified =
    start
    , λ n start≤n →
        let
          count : ℕ
          count =
            n ℕ.∸ start

          count+start≡n :
            count ℕ.+ start ≡ n
          count+start≡n =
            ℕ.≤-∸-+-cancel start≤n

          aAtN :
            partialSum a n ≡
            partialSum a start
              + partialSum
                  (dropSeries start a) count
          aAtN =
            cong (partialSum a)
              (sym count+start≡n)
            ∙ partialSum-drop-recombine
                start a count

          bAtN :
            partialSum b n ≡
            partialSum b start
              + partialSum
                  (dropSeries start b) count
          bAtN =
            cong (partialSum b)
              (sym count+start≡n)
            ∙ partialSum-drop-recombine
                start b count
        in
          cong (_+ correction) aAtN
          ∙ cong
              (λ tail →
                (partialSum a start + tail)
                  + correction)
              (tailPartialSumsEqual count)
          ∙ correctionReorder
              (partialSum a start)
              (partialSum b start)
              (partialSum
                (dropSeries start b) count)
          ∙ sym bAtN

eventuallyEqualSeriesHasSum :
  ∀ a b →
  (eventual : EventuallyEqualSeq a b) →
  ∀ value →
  HasSum a value →
  HasSum b
    ( value
    + (partialSum b (fst eventual)
      - partialSum a (fst eventual))
    )
eventuallyEqualSeriesHasSum
  a b eventual@(start , equal)
  value a-sum =
    eventuallyEqualSeqPresIsLimitSeq
      correctedPartialSums
      (partialSum b)
      correctedValue
      correctedEqualsModified
      correctedLimit
  where
  correction : ℝ
  correction =
    partialSum b start
      - partialSum a start

  correctedValue : ℝ
  correctedValue =
    value + correction

  correctedPartialSums : RealSequence
  correctedPartialSums n =
    partialSum a n + correction

  correctedLimit :
    isLimitSeq
      correctedPartialSums correctedValue
  correctedLimit =
    addPresIsLimitSeq
      (partialSum a)
      (λ _ → correction)
      value correction
      a-sum
      (constantIsLimitSeq correction)

  tailsPointwise : ∀ n →
    dropSeries start a n ≡
    dropSeries start b n
  tailsPointwise n =
    equal (n ℕ.+ start) ℕ.≤SumRight

  tailPartialSumsEqual : ∀ n →
    partialSum (dropSeries start a) n ≡
    partialSum (dropSeries start b) n
  tailPartialSumsEqual =
    partialSum-pointwise
      (dropSeries start a)
      (dropSeries start b)
      tailsPointwise

  correctedEqualsModified :
    EventuallyEqualSeq
      correctedPartialSums
      (partialSum b)
  correctedEqualsModified =
    start
    , λ n start≤n →
        let
          count : ℕ
          count =
            n ℕ.∸ start

          count+start≡n :
            count ℕ.+ start ≡ n
          count+start≡n =
            ℕ.≤-∸-+-cancel start≤n

          aAtN :
            partialSum a n ≡
            partialSum a start
              + partialSum
                  (dropSeries start a) count
          aAtN =
            cong (partialSum a)
              (sym count+start≡n)
            ∙ partialSum-drop-recombine
                start a count

          bAtN :
            partialSum b n ≡
            partialSum b start
              + partialSum
                  (dropSeries start b) count
          bAtN =
            cong (partialSum b)
              (sym count+start≡n)
            ∙ partialSum-drop-recombine
                start b count
        in
          cong (_+ correction) aAtN
          ∙ cong
              (λ tail →
                (partialSum a start + tail)
                  + correction)
              (tailPartialSumsEqual count)
          ∙ correctionReorder
              (partialSum a start)
              (partialSum b start)
              (partialSum
                (dropSeries start b) count)
          ∙ sym bAtN

eventuallyEqualSeriesPresSummable :
  ∀ a b →
  (eventual : EventuallyEqualSeq a b) →
  Summable a →
  Summable b
eventuallyEqualSeriesPresSummable
  a b eventual a-summable =
    seriesSum a a-summable
      + (partialSum b (fst eventual)
        - partialSum a (fst eventual))
    , eventuallyEqualSeriesHasSum
        a b eventual
        (seriesSum a a-summable)
        (seriesSumHasSum a a-summable)

seriesSum-finiteModification :
  ∀ a b →
  (eventual : EventuallyEqualSeq a b) →
  (a-summable : Summable a) →
  (b-summable : Summable b) →
  seriesSum b b-summable ≡
  seriesSum a a-summable
    + (partialSum b (fst eventual)
      - partialSum a (fst eventual))
seriesSum-finiteModification
  a b eventual a-summable b-summable =
    seriesSumIndependent
      b b-summable
      (eventuallyEqualSeriesPresSummable
        a b eventual a-summable)
