module Cubical.Analysis.Complex.Norm.Continuity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Relation.Premetric.Mappings
open CategoryStructures
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Norm

-- The l1 norm is continuous for the library's product premetric. Reuse
-- coordinate continuity and the real absolute-value and addition maps.
opaque
  normℂ-isContinuous : isContinuous (ℂPremetricSpace .snd) normℂ (ℝPremetricSpace .snd)
  normℂ-isContinuous = addOfContinuousIsContinuous (ℂPremetricSpace .snd)
    (absℝ ∘ re) (absℝ ∘ im)
    (snd (_∘C_ {M = ℂPremetricSpace} {N = ℝPremetricSpace} {O = ℝPremetricSpace}
      (absℝ , abs-isContinuous) (re , reℂ-isContinuous)))
    (snd (_∘C_ {M = ℂPremetricSpace} {N = ℝPremetricSpace} {O = ℝPremetricSpace}
      (absℝ , abs-isContinuous) (im , imℂ-isContinuous)))
