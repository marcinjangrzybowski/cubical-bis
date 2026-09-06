module Cubical.Analysis.Real.Series.Tails where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc)

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AdditiveGroup.Properties
  using (subAddCancel)
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Series.Base

open import Cubical.Relation.Premetric.Properties


private
  module ℝTheory = PremetricTheory ℝPremetricSpace

  shiftSeqWitness : ∀ start sequence →
    SeqWitness sequence →
    SeqWitness (shiftSequence start sequence)
  shiftSeqWitness start sequence =
    PT.map (ℝTheory.shiftPresIsCauchySeq start sequence)

  eventuallyEqualSeqWitness : ∀ a b →
    ℝTheory.EventuallyEqualSeq a b →
    SeqWitness a → SeqWitness b
  eventuallyEqualSeqWitness a b eventual =
    PT.map
      (ℝTheory.eventuallyEqualSeqPresIsCauchySeq
        a b eventual)

  subSeqWitness : ∀ {a b} →
    SeqWitness a → SeqWitness b →
    SeqWitness (λ n → a n - b n)
  subSeqWitness a-cauchy b-cauchy =
    addSeqWitness a-cauchy (negSeqWitness b-cauchy)


-- Dropping `start` terms reindexes the remaining tail from zero.

dropSeries : ℕ → RealSequence → RealSequence
dropSeries start terms n = terms (n ℕ.+ start)


partialSumShiftDifference :
  (terms : RealSequence) → (start count : ℕ) →
  partialSum terms (count ℕ.+ start)
    - partialSum terms start ≡
  partialSum (dropSeries start terms) count
partialSumShiftDifference terms start zero =
  subSelf (partialSum terms start)
partialSumShiftDifference terms start (suc count) =
  cong (_+ (- partialSum terms start))
    (addComm
      (partialSum terms (count ℕ.+ start))
      (terms (count ℕ.+ start)))
  ∙ sym
      (addAssoc
        (terms (count ℕ.+ start))
        (partialSum terms (count ℕ.+ start))
        (- partialSum terms start))
  ∙ cong (terms (count ℕ.+ start) +_)
      (partialSumShiftDifference terms start count)
  ∙ addComm
      (terms (count ℕ.+ start))
      (partialSum (dropSeries start terms) count)


partialSum-drop : ∀ start terms n →
  partialSum (dropSeries start terms) n ≡
  partialSum terms (n ℕ.+ start)
    - partialSum terms start
partialSum-drop start terms n =
  sym (partialSumShiftDifference terms start n)


partialSum-drop-recombine : ∀ start terms n →
  partialSum terms (n ℕ.+ start) ≡
  partialSum terms start
    + partialSum (dropSeries start terms) n
partialSum-drop-recombine start terms n =
  sym
    (subAddCancel
      (partialSum terms (n ℕ.+ start))
      (partialSum terms start))
  ∙ cong (_+ partialSum terms start)
      (partialSumShiftDifference terms start n)
  ∙ addComm
      (partialSum (dropSeries start terms) n)
      (partialSum terms start)


dropSeriesIsCauchy : ∀ start terms →
  IsCauchySeries terms →
  IsCauchySeries (dropSeries start terms)
dropSeriesIsCauchy start terms terms-cauchy =
  eventuallyEqualSeqWitness
    translatedShift
    (partialSum (dropSeries start terms))
    (0 , λ n _ → translatedShiftEqualsTail n)
    translatedShiftCauchy
  where
  partialSums : RealSequence
  partialSums = partialSum terms

  shiftedPartialSums : RealSequence
  shiftedPartialSums = shiftSequence start partialSums

  translatedShift : RealSequence
  translatedShift n =
    shiftedPartialSums n - partialSums start

  translatedShiftCauchy : SeqWitness translatedShift
  translatedShiftCauchy =
    subSeqWitness
      (shiftSeqWitness start partialSums terms-cauchy)
      (constantSeqWitness (partialSums start))

  translatedShiftEqualsTail : ∀ n →
    translatedShift n ≡
    partialSum (dropSeries start terms) n
  translatedShiftEqualsTail n =
    cong (_- partialSums start)
      (cong partialSums (ℕ.+-comm start n))
    ∙ sym (partialSum-drop start terms n)


dropSeriesHasSum : ∀ start terms value →
  HasSum terms value →
  HasSum
    (dropSeries start terms)
    (value - partialSum terms start)
dropSeriesHasSum start terms value terms-sum =
  subst
    (λ sequence →
      isLimitSequence sequence
        (value - partialSums start))
    (funExt translatedShiftEqualsTail)
    translatedShiftLimit
  where
  partialSums : RealSequence
  partialSums = partialSum terms

  shiftedPartialSums : RealSequence
  shiftedPartialSums = shiftSequence start partialSums

  translatedShift : RealSequence
  translatedShift n =
    shiftedPartialSums n - partialSums start

  translatedShiftLimit :
    isLimitSequence translatedShift
      (value - partialSums start)
  translatedShiftLimit =
    subPresIsLimitSequence
      (shiftPresIsLimitSequence
        start partialSums value terms-sum)
      (constantIsLimitSequence (partialSums start))

  translatedShiftEqualsTail : ∀ n →
    translatedShift n ≡
    partialSum (dropSeries start terms) n
  translatedShiftEqualsTail n =
    cong (_- partialSums start)
      (cong partialSums (ℕ.+-comm start n))
    ∙ sym (partialSum-drop start terms n)


dropSeriesReflectsHasSum : ∀ start terms tail-value →
  HasSum (dropSeries start terms) tail-value →
  HasSum
    terms
    (partialSum terms start + tail-value)
dropSeriesReflectsHasSum start terms tail-value tail-sum =
  shiftReflectsIsLimitSequence
    start partialSums
    (partialSums start + tail-value)
    shiftedPartialSumsLimit
  where
  partialSums : RealSequence
  partialSums = partialSum terms

  recombinedPartialSums : RealSequence
  recombinedPartialSums n =
    partialSums start
      + partialSum (dropSeries start terms) n

  recombinedPartialSumsLimit :
    isLimitSequence recombinedPartialSums
      (partialSums start + tail-value)
  recombinedPartialSumsLimit =
    addPresIsLimitSequence
      (constantIsLimitSequence (partialSums start))
      tail-sum

  recombinedEqualsShifted : ∀ n →
    recombinedPartialSums n ≡
    shiftSequence start partialSums n
  recombinedEqualsShifted n =
    sym (partialSum-drop-recombine start terms n)
    ∙ cong partialSums (ℕ.+-comm n start)

  shiftedPartialSumsLimit :
    isLimitSequence
      (shiftSequence start partialSums)
      (partialSums start + tail-value)
  shiftedPartialSumsLimit =
    subst
      (λ sequence →
        isLimitSequence sequence
          (partialSums start + tail-value))
      (funExt recombinedEqualsShifted)
      recombinedPartialSumsLimit


dropSeriesSummable : ∀ start terms →
  Summable terms →
  Summable (dropSeries start terms)
dropSeriesSummable start terms summable =
  seriesSum terms summable - partialSum terms start
  , dropSeriesHasSum start terms
      (seriesSum terms summable)
      (seriesSumHasSum terms summable)


dropSeriesReflectsSummable : ∀ start terms →
  Summable (dropSeries start terms) →
  Summable terms
dropSeriesReflectsSummable start terms tail-summable =
  partialSum terms start
    + seriesSum (dropSeries start terms) tail-summable
  , dropSeriesReflectsHasSum start terms
      (seriesSum (dropSeries start terms) tail-summable)
      (seriesSumHasSum
        (dropSeries start terms) tail-summable)


seriesSum-drop : ∀ start terms
  (summable : Summable terms)
  (tail-summable : Summable (dropSeries start terms)) →
  seriesSum (dropSeries start terms) tail-summable ≡
  seriesSum terms summable - partialSum terms start
seriesSum-drop start terms summable tail-summable =
  seriesSumIndependent
    (dropSeries start terms) tail-summable
    (dropSeriesSummable start terms summable)


seriesSum-from-drop : ∀ start terms
  (tail-summable : Summable (dropSeries start terms))
  (summable : Summable terms) →
  seriesSum terms summable ≡
  partialSum terms start
    + seriesSum (dropSeries start terms) tail-summable
seriesSum-from-drop start terms tail-summable summable =
  seriesSumIndependent terms summable
    (dropSeriesReflectsSummable
      start terms tail-summable)
