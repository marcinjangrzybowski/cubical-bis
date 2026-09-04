module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Damped.Limit.Continuity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Relation.Premetric.Mappings using (isContinuous)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Sequence


opaque
  dampedContinuousRealMapPreservesLimit :
    (function : ℝ → ℝ) →
    isContinuous
      (ℝPremetricSpace .snd) function
      (ℝPremetricSpace .snd) →
    ∀ {sequence limit} →
    isLimitSequence sequence limit →
    isLimitSequence (function ∘ sequence) (function limit)
  dampedContinuousRealMapPreservesLimit function continuous =
    continuousPreservesIsLimitSequence function continuous
