module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Bishop.Limit.Step where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Sequence


-- Consecutive differences of every convergent real sequence tend to zero.
-- This generic lemma isolates the sequential argument used by Bishop's
-- cosine iteration.

opaque
  convergentSuccessiveDifferences→zero :
    (sequence : ℕ → ℝ) (limit : ℝ) →
    isLimitSequence sequence limit →
    isLimitSequence
      (λ n →
        shiftSequence 1 sequence n - sequence n)
      0ℝ
  convergentSuccessiveDifferences→zero
      sequence limit sequence→limit =
    subst
      (isLimitSequence
        (λ n → shiftSequence 1 sequence n - sequence n))
      (subSelf limit)
      (subPresIsLimitSequence
        (shiftPresIsLimitSequence
          1 sequence limit sequence→limit)
        sequence→limit)
