module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Damped.Limit.Image where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma

open import Cubical.Analysis.Real.Algebra.Scalar.Base
open import Cubical.Analysis.Real.Sequence
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Damped.Iteration
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Damped.Limit.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Damped.Limit.Continuity
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Damped.Limit.ContinuityWitness


opaque
  dampedBishopPiHalfCosineTerms→candidateCosine :
    (candidate : DampedBishopPiHalfLimit) →
    isLimitSequence
      (cosℝ ∘ dampedBishopPiHalfApproximation)
      (cosℝ (dampedBishopPiHalfCandidate candidate))
  dampedBishopPiHalfCosineTerms→candidateCosine candidate =
    dampedContinuousRealMapPreservesLimit
      cosℝ dampedCosineIsContinuousOpaque
      {sequence = dampedBishopPiHalfApproximation}
      {limit = dampedBishopPiHalfCandidate candidate}
      (snd candidate)


opaque
  dampedBishopPiHalfTerms→candidateScaledCosine :
    (candidate : DampedBishopPiHalfLimit) →
    isLimitSequence dampedBishopPiHalfTerms
      (dampedBishopCoefficient ⋆
        cosℝ (dampedBishopPiHalfCandidate candidate))
  dampedBishopPiHalfTerms→candidateScaledCosine candidate =
    dampedContinuousRealMapPreservesLimit
      (dampedBishopCoefficient ⋆_)
      dampedHalfScalarIsContinuousOpaque
      {sequence = cosℝ ∘ dampedBishopPiHalfApproximation}
      {limit = cosℝ (dampedBishopPiHalfCandidate candidate)}
      (dampedBishopPiHalfCosineTerms→candidateCosine candidate)
