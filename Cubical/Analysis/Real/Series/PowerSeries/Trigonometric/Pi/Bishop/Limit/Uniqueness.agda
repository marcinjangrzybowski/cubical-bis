module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Bishop.Limit.Uniqueness where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Sequence


opaque
  limitSequenceUnique :
    (sequence : ℕ → ℝ) →
    (left right : ℝ) →
    isLimitSequence sequence left →
    isLimitSequence sequence right →
    left ≡ right
  limitSequenceUnique sequence left right left-limit right-limit =
    cong fst
      (isPropSequenceLimit sequence
        (left , left-limit)
        (right , right-limit))
