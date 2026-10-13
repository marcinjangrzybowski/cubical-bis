module Cubical.Analysis.Complex.Integration.LineIntegral.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Analysis.Real.Base using (ℝ)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Integration.Base
open import Cubical.Analysis.Complex.Integration.Path

-- The path package certifies that velocity is its actual derivative.
-- Parameter orientation is a ≤ b; geometric orientation is carried by the
-- path and its velocity, with no order or injectivity imposed on its image.
complexLineIntegrand : ∀ {a b} → (ℂ → ℂ) → UniformComplexPath a b → ℝ → ℂ
complexLineIntegrand f path t = f (UniformComplexPath.curve path t) ·ℂ UniformComplexPath.velocity path t

HasComplexLineIntegral : ∀ {a b} → (ℂ → ℂ) → UniformComplexPath a b → ℂ → Type₀
HasComplexLineIntegral {a} {b} f path = HasComplexRiemannIntegralOn (complexLineIntegrand f path) a b

IsComplexLineIntegrable : ∀ {a b} → (ℂ → ℂ) → UniformComplexPath a b → Type₀
IsComplexLineIntegrable {a} {b} f path = IsComplexRiemannIntegrableOn (complexLineIntegrand f path) a b

complexLineIntegral : ∀ {a b} (f : ℂ → ℂ) (path : UniformComplexPath a b) → IsComplexLineIntegrable f path → ℂ
complexLineIntegral f path = fst

isPropHasComplexLineIntegral : ∀ {a b} f (path : UniformComplexPath a b) value → isProp (HasComplexLineIntegral f path value)
isPropHasComplexLineIntegral {a} {b} f path = isPropHasComplexRiemannIntegralOn (complexLineIntegrand f path) a b

complexLineIntegralUnique : ∀ {a b} f (path : UniformComplexPath a b) value other →
  HasComplexLineIntegral f path value → HasComplexLineIntegral f path other → value ≡ other
complexLineIntegralUnique {a} {b} f path =
  complexRiemannIntegralUnique (complexLineIntegrand f path) a b (UniformComplexPath.ordered path)

isPropIsComplexLineIntegrable : ∀ {a b} f (path : UniformComplexPath a b) → isProp (IsComplexLineIntegrable f path)
isPropIsComplexLineIntegrable {a} {b} f path =
  isPropIsComplexRiemannIntegrableOn (complexLineIntegrand f path) a b (UniformComplexPath.ordered path)
