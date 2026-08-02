module Cubical.HITs.CauchyRealsP.Analysis.Series.Operations where

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
  Cubical.HITs.CauchyRealsP.Analysis.Series.FiniteSum

scaleSeries : ℝ → RealSequence → RealSequence
scaleSeries c terms n =
  c · terms n

partialSum-scale : ∀ c terms n →
  partialSum (scaleSeries c terms) n ≡
  c · partialSum terms n
partialSum-scale c terms zero =
  sym (mulZeroR c)
partialSum-scale c terms (suc n) =
  cong (_+ (c · terms n))
    (partialSum-scale c terms n)
  ∙ sym
      (mulDistR
        c (partialSum terms n) (terms n))

scaleHasSum : ∀ c terms value →
  HasSum terms value →
  HasSum (scaleSeries c terms) (c · value)
scaleHasSum c terms value terms-sum =
  eventuallyEqualSeqPresIsLimitSeq
    scaledPartialSums
    (partialSum (scaleSeries c terms))
    (c · value)
    (0 , λ n _ →
      sym (partialSum-scale c terms n))
    scaledLimit
  where
  scaledPartialSums : RealSequence
  scaledPartialSums n =
    c · partialSum terms n

  scaledLimit :
    isLimitSeq scaledPartialSums (c · value)
  scaledLimit =
    mulPresIsLimitSeq
      (λ _ → c)
      (partialSum terms)
      c value
      (constantIsLimitSeq c)
      terms-sum

scaleSummable : ∀ c terms →
  Summable terms →
  Summable (scaleSeries c terms)
scaleSummable c terms summable =
  c · seriesSum terms summable
  , scaleHasSum
      c terms
      (seriesSum terms summable)
      (seriesSumHasSum terms summable)

seriesSum-scale : ∀ c terms
  (summable : Summable terms)
  (scaled-summable :
    Summable (scaleSeries c terms)) →
  seriesSum (scaleSeries c terms)
      scaled-summable
    ≡
  c · seriesSum terms summable
seriesSum-scale c terms
  summable scaled-summable =
    seriesSumIndependent
      (scaleSeries c terms)
      scaled-summable
      (scaleSummable c terms summable)

rationalScaleSeriesIsCauchy :
  ∀ q terms →
  IsCauchySeries terms →
  IsCauchySeries
    (scaleSeries (rat q) terms)
rationalScaleSeriesIsCauchy
  q terms terms-cauchy =
    eventuallyEqualSeqPresIsCauchySeq
      (λ n →
        rat q · partialSum terms n)
      (partialSum
        (scaleSeries (rat q) terms))
      (0 , λ n _ →
        sym
          (partialSum-scale
            (rat q) terms n))
      (rationalScalePresIsCauchySeq
        q (partialSum terms) terms-cauchy)

dropSeries : ℕ → RealSequence → RealSequence
dropSeries start terms n =
  terms (n ℕ.+ start)

partialSum-drop : ∀ start terms n →
  partialSum (dropSeries start terms) n ≡
  partialSum terms (n ℕ.+ start)
    - partialSum terms start
partialSum-drop start terms n =
  sym
    (partialSumShiftDifference
      terms start n)

partialSum-drop-recombine : ∀ start terms n →
  partialSum terms (n ℕ.+ start) ≡
  partialSum terms start
    + partialSum (dropSeries start terms) n
partialSum-drop-recombine start terms n =
  sym
    (subAddCancel
      (partialSum terms (n ℕ.+ start))
      (partialSum terms start))
  ∙ cong
      (_+ partialSum terms start)
      (partialSumShiftDifference
        terms start n)
  ∙ addComm
      (partialSum (dropSeries start terms) n)
      (partialSum terms start)

dropSeriesIsCauchy : ∀ start terms →
  IsCauchySeries terms →
  IsCauchySeries (dropSeries start terms)
dropSeriesIsCauchy
  start terms terms-cauchy =
    eventuallyEqualSeqPresIsCauchySeq
      translatedShift
      (partialSum (dropSeries start terms))
      translatedShiftEqualsTail
      translatedShiftCauchy
  where
  partialSums : RealSequence
  partialSums =
    partialSum terms

  shiftedPartialSums : RealSequence
  shiftedPartialSums =
    shiftSeq start partialSums

  shiftedPartialSumsCauchy :
    isCauchySeq shiftedPartialSums
  shiftedPartialSumsCauchy =
    shiftPresIsCauchySeq
      start partialSums terms-cauchy

  translatedShift : RealSequence
  translatedShift n =
    shiftedPartialSums n
      - partialSums start

  translatedShiftCauchy :
    isCauchySeq translatedShift
  translatedShiftCauchy =
    subPresIsCauchySeq
      shiftedPartialSums
      (λ _ → partialSums start)
      shiftedPartialSumsCauchy
      (constantIsCauchySeq
        (partialSums start))

  translatedShiftEqualsTail :
    EventuallyEqualSeq
      translatedShift
      (partialSum (dropSeries start terms))
  translatedShiftEqualsTail =
    0
    , λ n _ →
        cong
          (_- partialSums start)
          (cong partialSums
            (ℕ.+-comm start n))
        ∙ sym (partialSum-drop start terms n)

dropSeriesHasSum : ∀ start terms value →
  HasSum terms value →
  HasSum
    (dropSeries start terms)
    (value - partialSum terms start)
dropSeriesHasSum
  start terms value terms-sum =
    eventuallyEqualSeqPresIsLimitSeq
      translatedShift
      (partialSum (dropSeries start terms))
      (value - partialSums start)
      translatedShiftEqualsTail
      translatedShiftLimit
  where
  partialSums : RealSequence
  partialSums =
    partialSum terms

  shiftedPartialSums : RealSequence
  shiftedPartialSums =
    shiftSeq start partialSums

  shiftedPartialSumsLimit :
    isLimitSeq shiftedPartialSums value
  shiftedPartialSumsLimit =
    shiftPresIsLimitSeq
      start partialSums value terms-sum

  translatedShift : RealSequence
  translatedShift n =
    shiftedPartialSums n
      - partialSums start

  translatedShiftLimit :
    isLimitSeq translatedShift
      (value - partialSums start)
  translatedShiftLimit =
    subPresIsLimitSeq
      shiftedPartialSums
      (λ _ → partialSums start)
      value (partialSums start)
      shiftedPartialSumsLimit
      (constantIsLimitSeq
        (partialSums start))

  translatedShiftEqualsTail :
    EventuallyEqualSeq
      translatedShift
      (partialSum (dropSeries start terms))
  translatedShiftEqualsTail =
    0
    , λ n _ →
        cong
          (_- partialSums start)
          (cong partialSums
            (ℕ.+-comm start n))
        ∙ sym (partialSum-drop start terms n)

dropSeriesReflectsHasSum : ∀ start terms tail-value →
  HasSum (dropSeries start terms) tail-value →
  HasSum
    terms
    (partialSum terms start + tail-value)
dropSeriesReflectsHasSum
  start terms tail-value tail-sum =
    shiftReflectsIsLimitSeq
      start partialSums
      (partialSums start + tail-value)
      shiftedPartialSumsLimit
  where
  partialSums : RealSequence
  partialSums =
    partialSum terms

  recombinedPartialSums : RealSequence
  recombinedPartialSums n =
    partialSums start
      + partialSum (dropSeries start terms) n

  recombinedPartialSumsLimit :
    isLimitSeq recombinedPartialSums
      (partialSums start + tail-value)
  recombinedPartialSumsLimit =
    addPresIsLimitSeq
      (λ _ → partialSums start)
      (partialSum (dropSeries start terms))
      (partialSums start) tail-value
      (constantIsLimitSeq (partialSums start))
      tail-sum

  recombinedEqualsShifted :
    EventuallyEqualSeq
      recombinedPartialSums
      (shiftSeq start partialSums)
  recombinedEqualsShifted =
    0
    , λ n _ →
        sym
          (partialSum-drop-recombine
            start terms n)
        ∙ cong partialSums
            (ℕ.+-comm n start)

  shiftedPartialSumsLimit :
    isLimitSeq
      (shiftSeq start partialSums)
      (partialSums start + tail-value)
  shiftedPartialSumsLimit =
    eventuallyEqualSeqPresIsLimitSeq
      recombinedPartialSums
      (shiftSeq start partialSums)
      (partialSums start + tail-value)
      recombinedEqualsShifted
      recombinedPartialSumsLimit

dropSeriesSummable : ∀ start terms →
  Summable terms →
  Summable (dropSeries start terms)
dropSeriesSummable start terms summable =
  seriesSum terms summable
    - partialSum terms start
  , dropSeriesHasSum
      start terms
      (seriesSum terms summable)
      (seriesSumHasSum terms summable)

dropSeriesReflectsSummable : ∀ start terms →
  Summable (dropSeries start terms) →
  Summable terms
dropSeriesReflectsSummable
  start terms tail-summable =
    partialSum terms start
      + seriesSum
          (dropSeries start terms)
          tail-summable
    , dropSeriesReflectsHasSum
        start terms
        (seriesSum
          (dropSeries start terms)
          tail-summable)
        (seriesSumHasSum
          (dropSeries start terms)
          tail-summable)

seriesSum-drop : ∀ start terms
  (summable : Summable terms)
  (tail-summable :
    Summable (dropSeries start terms)) →
  seriesSum (dropSeries start terms)
      tail-summable
    ≡
  seriesSum terms summable
    - partialSum terms start
seriesSum-drop start terms
  summable tail-summable =
    seriesSumIndependent
      (dropSeries start terms)
      tail-summable
      (dropSeriesSummable
        start terms summable)

seriesSum-from-drop : ∀ start terms
  (tail-summable :
    Summable (dropSeries start terms))
  (summable : Summable terms) →
  seriesSum terms summable
    ≡
  partialSum terms start
    + seriesSum
        (dropSeries start terms)
        tail-summable
seriesSum-from-drop start terms
  tail-summable summable =
    seriesSumIndependent
      terms summable
      (dropSeriesReflectsSummable
        start terms tail-summable)
