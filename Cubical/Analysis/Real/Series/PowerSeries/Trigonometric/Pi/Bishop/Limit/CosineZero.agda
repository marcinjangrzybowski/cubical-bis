module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Bishop.Limit.CosineZero where

open import Cubical.Foundations.Prelude
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Bishop.Iteration
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Bishop.Limit.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Bishop.Limit.CosineTerms
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Bishop.Limit.CosineContinuity
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Bishop.Limit.Uniqueness


opaque
  bishopPiHalfLimit-cosineZero :
    (candidate : BishopPiHalfLimit) →
    cosℝ (bishopPiHalfCandidate candidate) ≡ 0ℝ
  bishopPiHalfLimit-cosineZero candidate =
    limitSequenceUnique
      bishopPiHalfCosineTerms
      (cosℝ (bishopPiHalfCandidate candidate))
      0ℝ
      (bishopPiHalfCosineTerms→candidateCosine candidate)
      (bishopPiHalfCosineTerms→zero candidate)
