module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Damped.Limit.Terms where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma

open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Sequence
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Damped.Iteration
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Damped.Limit.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Damped.Limit.Step


opaque
  dampedBishopPiHalfTerms→zero :
    (candidate : DampedBishopPiHalfLimit) →
    isLimitSequence dampedBishopPiHalfTerms 0ℝ
  dampedBishopPiHalfTerms→zero candidate =
    subst
      (λ sequence → isLimitSequence sequence 0ℝ)
      (funExt dampedBishopPiHalfApproximation-difference)
      (dampedConvergentSuccessiveDifferences→zero
        dampedBishopPiHalfApproximation
        (dampedBishopPiHalfCandidate candidate)
        (snd candidate))
