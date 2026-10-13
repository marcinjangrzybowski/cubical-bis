module Cubical.Analysis.Complex.Integration.LineIntegral.Along where

open import Cubical.Foundations.Prelude
open import Cubical.Analysis.Real.Base using (ℝ)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Integration.Base
open import Cubical.Analysis.Complex.Integration.Path

-- Integrand values supplied along a curve, useful for reciprocals and
-- domain-local functions whose ambient total extension is unavailable.
-- Ordinary HasComplexLineIntegral is this predicate with h(t)=f(γ(t)).
complexLineIntegrandAlong : ∀ {a b} → (ℝ → ℂ) → UniformComplexPath a b → ℝ → ℂ
complexLineIntegrandAlong h path t = h t ·ℂ UniformComplexPath.velocity path t

HasComplexLineIntegralAlong : ∀ {a b} → (ℝ → ℂ) → UniformComplexPath a b → ℂ → Type₀
HasComplexLineIntegralAlong {a} {b} h path = HasComplexRiemannIntegralOn (complexLineIntegrandAlong h path) a b

IsComplexLineIntegrableAlong : ∀ {a b} → (ℝ → ℂ) → UniformComplexPath a b → Type₀
IsComplexLineIntegrableAlong {a} {b} h path = IsComplexRiemannIntegrableOn (complexLineIntegrandAlong h path) a b

complexLineIntegralAlongUnique : ∀ {a b} h (path : UniformComplexPath a b) v w →
  HasComplexLineIntegralAlong h path v → HasComplexLineIntegralAlong h path w → v ≡ w
complexLineIntegralAlongUnique {a} {b} h path =
  complexRiemannIntegralUnique (complexLineIntegrandAlong h path) a b (UniformComplexPath.ordered path)
