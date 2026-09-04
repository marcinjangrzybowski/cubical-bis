module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Damped.Limit.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Series.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Damped.Iteration


-- The analytic existence target is deliberately separated from the value
-- interface.  A Cauchy witness determines one proof-independent limit.

DampedBishopPiHalfCauchy : Type
DampedBishopPiHalfCauchy =
  SeqWitness dampedBishopPiHalfApproximation


DampedBishopPiHalfLimit : Type
DampedBishopPiHalfLimit =
  SequenceLimit dampedBishopPiHalfApproximation


isPropDampedBishopPiHalfLimit :
  isProp DampedBishopPiHalfLimit
isPropDampedBishopPiHalfLimit =
  isPropSequenceLimit dampedBishopPiHalfApproximation


dampedBishopPiHalfLimitFromCauchy :
  DampedBishopPiHalfCauchy → DampedBishopPiHalfLimit
dampedBishopPiHalfLimitFromCauchy =
  sequenceLimit dampedBishopPiHalfApproximation


dampedBishopPiHalfFromCauchy :
  DampedBishopPiHalfCauchy → ℝ
dampedBishopPiHalfFromCauchy =
  limitOfSequence dampedBishopPiHalfApproximation


dampedBishopPiFromCauchy :
  DampedBishopPiHalfCauchy → ℝ
dampedBishopPiFromCauchy cauchy =
  dampedBishopPiHalfFromCauchy cauchy +
    dampedBishopPiHalfFromCauchy cauchy


dampedBishopPiHalfCandidate :
  DampedBishopPiHalfLimit → ℝ
dampedBishopPiHalfCandidate = fst


dampedBishopPiCandidate :
  DampedBishopPiHalfLimit → ℝ
dampedBishopPiCandidate candidate =
  dampedBishopPiHalfCandidate candidate +
    dampedBishopPiHalfCandidate candidate


opaque
  dampedBishopPiHalfCandidate-unique :
    (left right : DampedBishopPiHalfLimit) →
    dampedBishopPiHalfCandidate left ≡
      dampedBishopPiHalfCandidate right
  dampedBishopPiHalfCandidate-unique left right =
    cong fst (isPropDampedBishopPiHalfLimit left right)


  dampedBishopPiCandidate-unique :
    (left right : DampedBishopPiHalfLimit) →
    dampedBishopPiCandidate left ≡
      dampedBishopPiCandidate right
  dampedBishopPiCandidate-unique left right =
    cong dampedBishopPiCandidate
      (isPropDampedBishopPiHalfLimit left right)


opaque
  dampedBishopPiHalfLimit-asSeries :
    (candidate : DampedBishopPiHalfLimit) →
    HasSum dampedBishopPiHalfTerms
      (dampedBishopPiHalfCandidate candidate)
  dampedBishopPiHalfLimit-asSeries candidate =
    subst
      (λ sequence →
        isLimitSequence sequence
          (dampedBishopPiHalfCandidate candidate))
      (funExt dampedBishopPiHalfApproximation-asPartialSum)
      (snd candidate)
