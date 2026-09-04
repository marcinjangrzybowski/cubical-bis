module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.ImageLimit where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Sequence
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire


opaque
  sineSequenceLimits-value :
    (source : ℕ → ℝ) →
    (source-limit target : ℝ) →
    isLimitSequence source source-limit →
    isLimitSequence (λ n → sinℝ (source n)) target →
    sinℝ source-limit ≡ target
  sineSequenceLimits-value
      source source-limit target source-converges image-limit =
    cong fst
      (isPropSequenceLimit image
        ( sinℝ source-limit
        , continuousPreservesIsLimitSequence
            sinℝ sinℝIsContinuous source-converges
        )
        (target , image-limit))
    where
    image : ℕ → ℝ
    image n = sinℝ (source n)


  sineSequenceLimit-value :
    (source : ℕ → ℝ) →
    (source-cauchy : SeqWitness source) →
    (target : ℝ) →
    isLimitSequence (λ n → sinℝ (source n)) target →
    sinℝ (lim source source-cauchy) ≡ target
  sineSequenceLimit-value source source-cauchy target image-limit =
    sineSequenceLimits-value
      source (lim source source-cauchy) target
      (lim-isLimitSeq source source-cauchy) image-limit
