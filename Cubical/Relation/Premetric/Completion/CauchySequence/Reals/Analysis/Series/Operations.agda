module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Operations where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat as ℕ using (ℕ ; zero ; suc)
import Cubical.Data.Nat.Order as ℕ

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Associativity
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.GroupLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Distributivity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Sequence
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base


scaleSeries : Real.ℝ → RealSequence → RealSequence
scaleSeries c terms n = c Mul.· terms n


partialSum-scale : ∀ c terms n →
  partialSum (scaleSeries c terms) n ≡
  c Mul.· partialSum terms n
partialSum-scale c terms zero =
  sym (mul-zero-right c)
partialSum-scale c terms (suc n) =
  cong (Add._+ (c Mul.· terms n))
    (partialSum-scale c terms n)
  ∙ sym
      (mul-distrib-over-add-right
        c (partialSum terms n) (terms n))


scaleHasSum : ∀ c terms value →
  HasSum terms value →
  HasSum (scaleSeries c terms) (c Mul.· value)
scaleHasSum c terms value terms-sum =
  eventuallyEqualPresIsLimitSequence
    ∣ 0 , (λ n _ → sym (partialSum-scale c terms n)) ∣₁
    (mulPresIsLimitSequence
      (constantIsLimitSequence c) terms-sum)


scaleSummable : ∀ c terms →
  Summable terms → Summable (scaleSeries c terms)
scaleSummable c terms summable =
  c Mul.· seriesSum terms summable
  , scaleHasSum c terms
      (seriesSum terms summable)
      (seriesSumHasSum terms summable)


seriesSum-scale : ∀ c terms
  (summable : Summable terms)
  (scaled-summable : Summable (scaleSeries c terms)) →
  seriesSum (scaleSeries c terms) scaled-summable ≡
  c Mul.· seriesSum terms summable
seriesSum-scale c terms summable scaled-summable =
  seriesSumIndependent
    (scaleSeries c terms) scaled-summable
    (scaleSummable c terms summable)


-- This strengthens the rational-scalar statement in the regular-real API.
-- A constant real sequence and the partial sums are native Cauchy, and the
-- already constructed real multiplication preserves such sequences.

scaleSeriesIsCauchy : ∀ c terms →
  IsCauchySeries terms →
  IsCauchySeries (scaleSeries c terms)
scaleSeriesIsCauchy c terms terms-cauchy =
  eventuallyEqualPresIsCauchySequence
    ∣ 0 , (λ n _ → sym (partialSum-scale c terms n)) ∣₁
    (mulPresIsCauchySequence
      (constantIsCauchySequence c) terms-cauchy)


-- Dropping a finite prefix ----------------------------------------------

dropSeries : ℕ → RealSequence → RealSequence
dropSeries start terms n = terms (n ℕ.+ start)


partialSumShiftDifference :
  (terms : RealSequence) → (start count : ℕ) →
  partialSum terms (count ℕ.+ start)
    Group.- partialSum terms start ≡
  partialSum (dropSeries start terms) count
partialSumShiftDifference terms start zero =
  sub-self (partialSum terms start)
partialSumShiftDifference terms start (suc count) =
    cong (Add._+ (Neg.- partialSum terms start))
      (add-comm
        (partialSum terms (count ℕ.+ start))
        (terms (count ℕ.+ start)))
  ∙ sym (add-assoc
      (terms (count ℕ.+ start))
      (partialSum terms (count ℕ.+ start))
      (Neg.- partialSum terms start))
  ∙ cong (terms (count ℕ.+ start) Add.+_)
      (partialSumShiftDifference terms start count)
  ∙ add-comm
      (terms (count ℕ.+ start))
      (partialSum (dropSeries start terms) count)


partialSum-drop : ∀ start terms n →
  partialSum (dropSeries start terms) n ≡
  partialSum terms (n ℕ.+ start)
    Group.- partialSum terms start
partialSum-drop start terms n =
  sym (partialSumShiftDifference terms start n)


partialSum-drop-recombine : ∀ start terms n →
  partialSum terms (n ℕ.+ start) ≡
  partialSum terms start Add.+
    partialSum (dropSeries start terms) n
partialSum-drop-recombine start terms n =
    sym (sub-add-cancel
      (partialSum terms (n ℕ.+ start))
      (partialSum terms start))
  ∙ cong (Add._+ partialSum terms start)
      (partialSumShiftDifference terms start n)
  ∙ add-comm
      (partialSum (dropSeries start terms) n)
      (partialSum terms start)


dropSeriesIsCauchy : ∀ start terms →
  IsCauchySeries terms →
  IsCauchySeries (dropSeries start terms)
dropSeriesIsCauchy start terms terms-cauchy =
  eventuallyEqualPresIsCauchySequence
    translated-shift-equals-tail
    translated-shift-cauchy
  where
  partialSums : RealSequence
  partialSums = partialSum terms

  shiftedPartialSums : RealSequence
  shiftedPartialSums = shiftSequence start partialSums

  translatedShift : RealSequence
  translatedShift n =
    shiftedPartialSums n Group.- partialSums start

  translated-shift-cauchy :
    IsCauchySequence translatedShift
  translated-shift-cauchy =
    subPresIsCauchySequence
      (shiftPresIsCauchySequence
        start partialSums terms-cauchy)
      (constantIsCauchySequence (partialSums start))

  translated-shift-equals-tail :
    EventuallyEqualSequence
      translatedShift
      (partialSum (dropSeries start terms))
  translated-shift-equals-tail =
    ∣ 0 , (λ n _ →
      cong (Group._- partialSums start)
        (cong partialSums (ℕ.+-comm start n))
      ∙ sym (partialSum-drop start terms n)) ∣₁


dropSeriesHasSum : ∀ start terms value →
  HasSum terms value →
  HasSum (dropSeries start terms)
    (value Group.- partialSum terms start)
dropSeriesHasSum start terms value terms-sum =
  eventuallyEqualPresIsLimitSequence
    translated-shift-equals-tail
    translated-shift-limit
  where
  partialSums : RealSequence
  partialSums = partialSum terms

  shiftedPartialSums : RealSequence
  shiftedPartialSums = shiftSequence start partialSums

  translatedShift : RealSequence
  translatedShift n =
    shiftedPartialSums n Group.- partialSums start

  translated-shift-limit :
    isLimitSequence translatedShift
      (value Group.- partialSums start)
  translated-shift-limit =
    subPresIsLimitSequence
      (shiftPresIsLimitSequence
        start partialSums value terms-sum)
      (constantIsLimitSequence (partialSums start))

  translated-shift-equals-tail :
    EventuallyEqualSequence
      translatedShift
      (partialSum (dropSeries start terms))
  translated-shift-equals-tail =
    ∣ 0 , (λ n _ →
      cong (Group._- partialSums start)
        (cong partialSums (ℕ.+-comm start n))
      ∙ sym (partialSum-drop start terms n)) ∣₁


dropSeriesReflectsHasSum : ∀ start terms tail-value →
  HasSum (dropSeries start terms) tail-value →
  HasSum terms
    (partialSum terms start Add.+ tail-value)
dropSeriesReflectsHasSum start terms tail-value tail-sum =
  shiftReflectsIsLimitSequence
    start partialSums
    (partialSums start Add.+ tail-value)
    shifted-partial-sums-limit
  where
  partialSums : RealSequence
  partialSums = partialSum terms

  recombinedPartialSums : RealSequence
  recombinedPartialSums n =
    partialSums start Add.+
      partialSum (dropSeries start terms) n

  recombined-partial-sums-limit :
    isLimitSequence recombinedPartialSums
      (partialSums start Add.+ tail-value)
  recombined-partial-sums-limit =
    addPresIsLimitSequence
      (constantIsLimitSequence (partialSums start))
      tail-sum

  recombined-equals-shifted :
    EventuallyEqualSequence
      recombinedPartialSums
      (shiftSequence start partialSums)
  recombined-equals-shifted =
    ∣ 0 , (λ n _ →
      sym (partialSum-drop-recombine start terms n)
      ∙ cong partialSums (ℕ.+-comm n start)) ∣₁

  shifted-partial-sums-limit :
    isLimitSequence
      (shiftSequence start partialSums)
      (partialSums start Add.+ tail-value)
  shifted-partial-sums-limit =
    eventuallyEqualPresIsLimitSequence
      recombined-equals-shifted
      recombined-partial-sums-limit


dropSeriesSummable : ∀ start terms →
  Summable terms → Summable (dropSeries start terms)
dropSeriesSummable start terms summable =
  seriesSum terms summable Group.- partialSum terms start
  , dropSeriesHasSum start terms
      (seriesSum terms summable)
      (seriesSumHasSum terms summable)


dropSeriesReflectsSummable : ∀ start terms →
  Summable (dropSeries start terms) → Summable terms
dropSeriesReflectsSummable start terms tail-summable =
  partialSum terms start Add.+
    seriesSum (dropSeries start terms) tail-summable
  , dropSeriesReflectsHasSum start terms
      (seriesSum (dropSeries start terms) tail-summable)
      (seriesSumHasSum (dropSeries start terms) tail-summable)


seriesSum-drop : ∀ start terms
  (summable : Summable terms)
  (tail-summable : Summable (dropSeries start terms)) →
  seriesSum (dropSeries start terms) tail-summable ≡
  seriesSum terms summable Group.- partialSum terms start
seriesSum-drop start terms summable tail-summable =
  seriesSumIndependent
    (dropSeries start terms) tail-summable
    (dropSeriesSummable start terms summable)


seriesSum-from-drop : ∀ start terms
  (tail-summable : Summable (dropSeries start terms))
  (summable : Summable terms) →
  seriesSum terms summable ≡
  partialSum terms start Add.+
    seriesSum (dropSeries start terms) tail-summable
seriesSum-from-drop start terms tail-summable summable =
  seriesSumIndependent terms summable
    (dropSeriesReflectsSummable start terms tail-summable)
