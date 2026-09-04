module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Damped.Limit.Step where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Sequence


opaque
  dampedConvergentSuccessiveDifferences→zero :
    (sequence : ℕ → ℝ) (limit : ℝ) →
    isLimitSequence sequence limit →
    isLimitSequence
      (λ n →
        shiftSequence 1 sequence n - sequence n)
      0ℝ
  dampedConvergentSuccessiveDifferences→zero
      sequence limit sequence→limit =
    subst
      (isLimitSequence
        (λ n → shiftSequence 1 sequence n - sequence n))
      (subSelf limit)
      (subPresIsLimitSequence
        (shiftPresIsLimitSequence
          1 sequence limit sequence→limit)
        sequence→limit)
