module Cubical.Analysis.Complex.Transcendental.Logarithm.Uniform where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open import Cubical.Relation.Premetric.Base
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Integration.UniformContinuity
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Calculus.Derivative.Uniform
open import Cubical.Analysis.Complex.Calculus.Derivative.Uniform.Inverse
open import Cubical.Analysis.Complex.Transcendental.Exponential.Base
open import Cubical.Analysis.Complex.Transcendental.Exponential.Uniform

-- Any supplied continuous logarithmic branch has the reciprocal derivative
-- on a quantitatively bounded domain. Only exp(log z)=z, continuity and
-- bounds are assumed; differentiability of the logarithm is a conclusion.
-- The source may be a local domain or an interval parameterizing a lift.
opaque
  logarithmBranchHasUniformDerivativeAlong : ∀ {ℓ ℓ'} {A : Type ℓ} (source : PremetricStr ℓ' A)
    (coordinate logarithm reciprocal : A → ℂ) (B C : ℚ₊) →
    (∀ x → expℂ (logarithm x) ≡ coordinate x) →
    (∀ x → reciprocal x ·ℂ coordinate x ≡ 1ℂ) →
    (∀ x → normℂ (coordinate x) ≤ℝ rat (fst B)) →
    (∀ x → normℂ (reciprocal x) ≤ℝ rat (fst C)) →
    IsRadiuswiseUniformlyContinuous source logarithm (ℂPremetricSpace .snd) →
    IsRadiuswiseUniformComplexDerivativeAlong source coordinate logarithm reciprocal
  logarithmBranchHasUniformDerivativeAlong source coordinate logarithm reciprocal B C exponentialLaw reciprocalLaw
    boundedCoordinate boundedReciprocal continuous =
    uniformInverseComplexDerivativeAlong source coordinate logarithm coordinate reciprocal C reciprocalLaw boundedReciprocal
      (subst (λ h → IsRadiuswiseUniformComplexDerivativeAlong source logarithm h h) (funExt exponentialLaw)
        (expℂHasUniformDerivativeAlongBounded source logarithm B
          (λ x → subst (λ z → normℂ z ≤ℝ rat (fst B)) (sym (exponentialLaw x)) (boundedCoordinate x)) continuous))
