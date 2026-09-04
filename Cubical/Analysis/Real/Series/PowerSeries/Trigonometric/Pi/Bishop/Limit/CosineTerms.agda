module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Bishop.Limit.CosineTerms where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma

open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Sequence
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Bishop.Iteration
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Bishop.Limit.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Bishop.Limit.Step


opaque
  bishopPiHalfCosineTerms→zero :
    (candidate : BishopPiHalfLimit) →
    isLimitSequence bishopPiHalfCosineTerms 0ℝ
  bishopPiHalfCosineTerms→zero candidate =
    subst
      (λ sequence → isLimitSequence sequence 0ℝ)
      (funExt bishopPiHalfApproximation-difference)
      (convergentSuccessiveDifferences→zero
        bishopPiHalfApproximation
        (bishopPiHalfCandidate candidate)
        (snd candidate))
