module Cubical.Analysis.Complex.Integration.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Analysis.Real.Base using (ℝ)
open import Cubical.Analysis.Real.Order.Base
import Cubical.Analysis.Real.Integration.RiemannIntegral.Base as Real
import Cubical.Analysis.Real.Integration.RiemannIntegral.Extensionality as Real
open import Cubical.Analysis.Complex.Base

-- Complex-valued integration over an ordered real parameter interval is
-- exactly the pair of native real Riemann integrals, with their existing
-- tagged-partition semantics. In particular this is not defined by an
-- antiderivative or an endpoint difference.
HasComplexRiemannIntegralOn : (ℝ → ℂ) → ℝ → ℝ → ℂ → Type₀
HasComplexRiemannIntegralOn f a b value =
  Real.HasRiemannIntegralOn (re ∘ f) a b (re value) × Real.HasRiemannIntegralOn (im ∘ f) a b (im value)

IsComplexRiemannIntegrableOn : (ℝ → ℂ) → ℝ → ℝ → Type₀
IsComplexRiemannIntegrableOn f a b = Σ[ value ∈ ℂ ] HasComplexRiemannIntegralOn f a b value

complexIntegral : ∀ {f a b} → IsComplexRiemannIntegrableOn f a b → ℂ
complexIntegral = fst

isPropHasComplexRiemannIntegralOn : ∀ f a b value → isProp (HasComplexRiemannIntegralOn f a b value)
isPropHasComplexRiemannIntegralOn f a b value = isProp×
  (Real.isPropHasRiemannIntegralOn (re ∘ f) a b (re value))
  (Real.isPropHasRiemannIntegralOn (im ∘ f) a b (im value))

complexRiemannIntegralUnique : ∀ f a b → a ≤ℝ b → ∀ value other →
  HasComplexRiemannIntegralOn f a b value → HasComplexRiemannIntegralOn f a b other → value ≡ other
complexRiemannIntegralUnique f a b ordered value other first second = ℂ≡
  (Real.riemannIntegralUnique a b ordered (re ∘ f) (re value) (re other) (fst first) (fst second))
  (Real.riemannIntegralUnique a b ordered (im ∘ f) (im value) (im other) (snd first) (snd second))

isPropIsComplexRiemannIntegrableOn : ∀ f a b → a ≤ℝ b → isProp (IsComplexRiemannIntegrableOn f a b)
isPropIsComplexRiemannIntegrableOn f a b ordered (value , proof) (other , proof') =
  Σ≡Prop (isPropHasComplexRiemannIntegralOn f a b) (complexRiemannIntegralUnique f a b ordered value other proof proof')

complexIntegralIndependent : ∀ f a b → a ≤ℝ b → (first second : IsComplexRiemannIntegrableOn f a b) →
  complexIntegral {f = f} {a = a} {b = b} first ≡ complexIntegral {f = f} {a = a} {b = b} second
complexIntegralIndependent f a b ordered first second = cong fst (isPropIsComplexRiemannIntegrableOn f a b ordered first second)

complexHasIntegralCongOn : ∀ f g a b value →
  (∀ x → a ≤ℝ x → x ≤ℝ b → f x ≡ g x) →
  HasComplexRiemannIntegralOn f a b value → HasComplexRiemannIntegralOn g a b value
complexHasIntegralCongOn f g a b value agree proof =
  Real.hasRiemannIntegral-congOn (re ∘ f) (re ∘ g) a b (re value)
    (λ x lower upper → cong re (agree x lower upper)) (fst proof) ,
  Real.hasRiemannIntegral-congOn (im ∘ f) (im ∘ g) a b (im value)
    (λ x lower upper → cong im (agree x lower upper)) (snd proof)
