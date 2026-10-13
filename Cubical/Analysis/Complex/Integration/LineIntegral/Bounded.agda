module Cubical.Analysis.Complex.Integration.LineIntegral.Bounded where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Real.Integration.UniformContinuity
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Integration.Path
open import Cubical.Analysis.Complex.Integration.LineIntegral.Base
open import Cubical.Analysis.Complex.Integration.LineIntegral.FundamentalTheorem

open import Cubical.Analysis.Complex.Integration.UniformContinuity.Bounded public

IsBoundedUniformPrimitiveAlongPath : ∀ {a b} → (ℂ → ℂ) → (ℂ → ℂ) → UniformComplexPath a b → Type₀
IsBoundedUniformPrimitiveAlongPath {a} {b} F f path =
  IsUniformPrimitiveAlongPath F f path ×
  (∃[ B ∈ ℚ₊ ] (∀ t → a ≤ℝ t → t ≤ℝ b → normℂ (f (UniformComplexPath.curve path t)) ≤ℝ rat (fst B)))

boundedUniformPrimitiveHasComplexLineIntegral : ∀ {a b} (path : UniformComplexPath a b) F f →
  IsBoundedUniformPrimitiveAlongPath F f path →
  HasComplexLineIntegral f path (F (pathFinish path) -ℂ F (pathStart path))
boundedUniformPrimitiveHasComplexLineIntegral path F f (estimate , bounded) =
  PT.rec (isPropHasComplexLineIntegral f path (F (pathFinish path) -ℂ F (pathStart path)))
    (λ { (B , bound) → fundamentalTheoremOfComplexLineIntegrals path F f B bound estimate }) bounded

continuousUniformPrimitiveIsBounded : ∀ {a b} (path : UniformComplexPath a b) F f →
  IsUniformPrimitiveAlongPath F f path →
  IsRadiuswiseUniformlyContinuous (ClosedIntervalPremetricSpace a b .snd)
    (f ∘ UniformComplexPath.curve path ∘ fst) (ℂPremetricSpace .snd) →
  IsBoundedUniformPrimitiveAlongPath F f path
continuousUniformPrimitiveIsBounded {a} {b} path F f estimate continuous = estimate ,
  radiuswiseComplexUniformContinuityIsBoundedOn (f ∘ UniformComplexPath.curve path) a b (UniformComplexPath.ordered path) continuous

-- Radiuswise uniform continuity of the integrand along the curve discharges
-- the separate bound in the FTC. It is weaker than supplying a global modulus.
continuousUniformPrimitiveHasComplexLineIntegral : ∀ {a b} (path : UniformComplexPath a b) F f →
  IsUniformPrimitiveAlongPath F f path →
  IsRadiuswiseUniformlyContinuous (ClosedIntervalPremetricSpace a b .snd)
    (f ∘ UniformComplexPath.curve path ∘ fst) (ℂPremetricSpace .snd) →
  HasComplexLineIntegral f path (F (pathFinish path) -ℂ F (pathStart path))
continuousUniformPrimitiveHasComplexLineIntegral path F f estimate continuous =
  boundedUniformPrimitiveHasComplexLineIntegral path F f (continuousUniformPrimitiveIsBounded path F f estimate continuous)
