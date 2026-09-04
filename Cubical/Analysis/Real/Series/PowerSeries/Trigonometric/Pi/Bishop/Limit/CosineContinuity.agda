module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Bishop.Limit.CosineContinuity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma

open import Cubical.Analysis.Real.Sequence
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Bishop.Iteration
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Bishop.Limit.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Bishop.Limit.Continuity
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Bishop.Limit.CosineContinuityWitness


opaque
  bishopPiHalfCosineTerms→candidateCosine :
    (candidate : BishopPiHalfLimit) →
    isLimitSequence (cosℝ ∘ bishopPiHalfApproximation)
      (cosℝ (bishopPiHalfCandidate candidate))
  bishopPiHalfCosineTerms→candidateCosine candidate =
    continuousRealMapPreservesLimit
      cosℝ cosℝIsContinuousOpaque
      {sequence = bishopPiHalfApproximation}
      {limit = bishopPiHalfCandidate candidate}
      (snd candidate)
