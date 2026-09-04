module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Bishop.Limit.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Series.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Bishop.Iteration


-- This is the exact remaining existence target for Bishop's construction.
-- Once inhabited, completeness turns it into the unique limit below.

BishopPiHalfCauchy : Type
BishopPiHalfCauchy =
  SeqWitness bishopPiHalfApproximation


BishopPiHalfLimit : Type
BishopPiHalfLimit =
  SequenceLimit bishopPiHalfApproximation


isPropBishopPiHalfLimit :
  isProp BishopPiHalfLimit
isPropBishopPiHalfLimit =
  isPropSequenceLimit bishopPiHalfApproximation


bishopPiHalfLimitFromCauchy :
  BishopPiHalfCauchy → BishopPiHalfLimit
bishopPiHalfLimitFromCauchy =
  sequenceLimit bishopPiHalfApproximation


bishopPiHalfFromCauchy :
  BishopPiHalfCauchy → ℝ
bishopPiHalfFromCauchy =
  limitOfSequence bishopPiHalfApproximation


bishopPiFromCauchy :
  BishopPiHalfCauchy → ℝ
bishopPiFromCauchy cauchy =
  bishopPiHalfFromCauchy cauchy +
    bishopPiHalfFromCauchy cauchy


bishopPiHalfCandidate :
  BishopPiHalfLimit → ℝ
bishopPiHalfCandidate = fst


bishopPiCandidate :
  BishopPiHalfLimit → ℝ
bishopPiCandidate candidate =
  bishopPiHalfCandidate candidate +
    bishopPiHalfCandidate candidate


opaque
  bishopPiHalfCandidate-unique :
    (left right : BishopPiHalfLimit) →
    bishopPiHalfCandidate left ≡
      bishopPiHalfCandidate right
  bishopPiHalfCandidate-unique left right =
    cong fst (isPropBishopPiHalfLimit left right)


  bishopPiCandidate-unique :
    (left right : BishopPiHalfLimit) →
    bishopPiCandidate left ≡ bishopPiCandidate right
  bishopPiCandidate-unique left right =
    cong bishopPiCandidate
      (isPropBishopPiHalfLimit left right)


opaque
  bishopPiHalfLimit-asCosineSeries :
    (candidate : BishopPiHalfLimit) →
    HasSum bishopPiHalfCosineTerms
      (bishopPiHalfCandidate candidate)
  bishopPiHalfLimit-asCosineSeries candidate =
    subst
      (λ sequence →
        isLimitSequence sequence
          (bishopPiHalfCandidate candidate))
      (funExt bishopPiHalfApproximation-asPartialSum)
      (snd candidate)
