module Cubical.Analysis.Complex.Transcendental.Exponential.Continuity where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Premetric.Mappings
open CategoryStructures
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Functions.Exponential
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Continuity
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Continuity
open import Cubical.Analysis.Complex.Continuity.Algebra
open import Cubical.Analysis.Complex.Polar.Cis
open import Cubical.Analysis.Complex.Polar.Cis.Continuity
open import Cubical.Analysis.Complex.Transcendental.Exponential.Base

opaque
  expℂ-isContinuous : isContinuous (ℂPremetricSpace .snd) expℂ (ℂPremetricSpace .snd)
  expℂ-isContinuous = subst
    (λ f → isContinuous (ℂPremetricSpace .snd) f (ℂPremetricSpace .snd))
    (sym (funExt expℂ-polar))
    (mulOfComplexContinuous (ℂPremetricSpace .snd) _ _
    (snd ((fromℝ , fromℝ-isContinuous) ∘C
      ((expℝ , exponentialEntireValueIsContinuous) ∘C (_ , reℂ-isContinuous))))
    (snd ((cisℝ , cisℝ-isContinuous) ∘C (_ , imℂ-isContinuous))))
