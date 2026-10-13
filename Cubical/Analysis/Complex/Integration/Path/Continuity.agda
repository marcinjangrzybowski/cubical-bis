module Cubical.Analysis.Complex.Integration.Path.Continuity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Analysis.Real.Base using (ℝ)
open import Cubical.Analysis.Real.Domain.Interval using (ClosedIntervalPremetricSpace)
open import Cubical.Analysis.Real.Integration.UniformContinuity
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Integration.Curve
open import Cubical.Analysis.Complex.Integration.Path

module _ {a b : ℝ} (path : UniformComplexPath a b) where
  private module P = UniformComplexPath path

  opaque
    pathIsUniformlyContinuous :
      isUniformlyContinuous (ClosedIntervalPremetricSpace a b .snd) (P.curve ∘ fst) (ℂPremetricSpace .snd)
    pathIsUniformlyContinuous = uniformComplexCurveIsUniformlyContinuousOn
      P.curve P.velocity a b P.speedBound P.differentiable P.boundedSpeed


  opaque
    pathIsRadiuswiseUniformlyContinuous :
      IsRadiuswiseUniformlyContinuous (ClosedIntervalPremetricSpace a b .snd) (P.curve ∘ fst) (ℂPremetricSpace .snd)
    pathIsRadiuswiseUniformlyContinuous = isUniformlyContinuous→isRadiuswiseUniformlyContinuous
      (ClosedIntervalPremetricSpace a b .snd) (P.curve ∘ fst) (ℂPremetricSpace .snd) pathIsUniformlyContinuous

