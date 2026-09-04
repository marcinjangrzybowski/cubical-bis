module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Bishop.Limit.Continuity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Sequence
open import Cubical.Relation.Premetric.Mappings using (isContinuous)


-- Keeping this general continuity step opaque prevents later proofs from
-- unfolding the concrete power-series continuity witnesses for sine/cosine.

opaque
  continuousRealMapPreservesLimit :
    (function : ℝ → ℝ) →
    isContinuous
      (ℝPremetricSpace .snd) function
      (ℝPremetricSpace .snd) →
    ∀ {sequence limit} →
    isLimitSequence sequence limit →
    isLimitSequence (function ∘ sequence) (function limit)
  continuousRealMapPreservesLimit function continuous =
    continuousPreservesIsLimitSequence function continuous
