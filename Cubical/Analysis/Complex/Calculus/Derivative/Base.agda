module Cubical.Analysis.Complex.Calculus.Derivative.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Metric

-- A complex-linear first-order approximation, measured in the l1 norm.
-- There is no division by an increment, and every radius exists only under
-- its own truncation. The coordinate permits later use on open subspaces.
complexDerivativeErrorAlong : ∀ {ℓ} {A : Type ℓ} →
  (coordinate function : A → ℂ) → ℂ → A → A → ℂ
complexDerivativeErrorAlong coordinate function value x y =
  (function y -ℂ function x) -ℂ value ·ℂ (coordinate y -ℂ coordinate x)

IsComplexDerivativeAlongAt : ∀ {ℓ ℓ'} {A : Type ℓ} →
  PremetricStr ℓ' A → (coordinate function : A → ℂ) → ℂ → A → Type (ℓ-max ℓ ℓ')
IsComplexDerivativeAlongAt source coordinate function value x =
  ∀ (ε : ℚ₊) → PT.∥ (Σ[ δ ∈ ℚ₊ ]
    (∀ y → PremetricStr._≈[_]_ source x δ y →
      normℂ (complexDerivativeErrorAlong coordinate function value x y)
        ≤ℝ rat (fst ε) · normℂ (coordinate y -ℂ coordinate x))) ∥₁

IsComplexDerivativeAlong : ∀ {ℓ ℓ'} {A : Type ℓ} →
  PremetricStr ℓ' A → (coordinate function derivative : A → ℂ) → Type (ℓ-max ℓ ℓ')
IsComplexDerivativeAlong source coordinate function derivative =
  ∀ x → IsComplexDerivativeAlongAt source coordinate function (derivative x) x

IsComplexDerivativeAt : (ℂ → ℂ) → ℂ → ℂ → Type₀
IsComplexDerivativeAt = IsComplexDerivativeAlongAt (ℂPremetricSpace .snd) (idfun ℂ)

IsComplexDerivative : (function derivative : ℂ → ℂ) → Type₀
IsComplexDerivative = IsComplexDerivativeAlong (ℂPremetricSpace .snd) (idfun ℂ)

isPropIsComplexDerivativeAlongAt : ∀ {ℓ ℓ'} {A : Type ℓ}
  (source : PremetricStr ℓ' A) coordinate function value x →
  isProp (IsComplexDerivativeAlongAt source coordinate function value x)
isPropIsComplexDerivativeAlongAt source coordinate function value x = isPropΠ λ _ → PT.squash₁

isPropIsComplexDerivativeAlong : ∀ {ℓ ℓ'} {A : Type ℓ}
  (source : PremetricStr ℓ' A) coordinate function derivative →
  isProp (IsComplexDerivativeAlong source coordinate function derivative)
isPropIsComplexDerivativeAlong source coordinate function derivative =
  isPropΠ λ x → isPropIsComplexDerivativeAlongAt source coordinate function (derivative x) x

-- This only pulls back a neighbourhood; it does not choose a global modulus.
pullbackComplexDerivativeAlong : ∀ {ℓA ℓA' ℓB ℓB'} {A : Type ℓA} {B : Type ℓB}
  (source : PremetricStr ℓA' A) (target : PremetricStr ℓB' B)
  (coordinate function derivative : B → ℂ) (map : A → B) →
  isContinuous source map target → IsComplexDerivativeAlong target coordinate function derivative →
  IsComplexDerivativeAlong source (coordinate ∘ map) (function ∘ map) (derivative ∘ map)
pullbackComplexDerivativeAlong source target coordinate function derivative map continuous differentiable x ε =
  PT.rec PT.squash₁ (λ { (δ , bound) →
    PT.map (λ { (η , near) → η , λ y close → bound (map y) (near y close) })
      (continuous x .IsContinuousAt.pres≈ δ) }) (differentiable (map x) ε)
