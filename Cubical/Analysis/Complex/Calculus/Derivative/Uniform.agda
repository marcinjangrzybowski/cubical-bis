module Cubical.Analysis.Complex.Calculus.Derivative.Uniform where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Relation.Premetric.Base
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Multiplication using (_·_)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Integration.UniformContinuity
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Calculus.Derivative.Base

-- Uniform in the points, with one truncated radius at each error tolerance.
-- The coordinate permits restriction to a path or a domain; no ambient
-- extension and no globally selected modulus are part of this predicate.
IsRadiuswiseUniformComplexDerivativeAlong : ∀ {ℓ ℓ'} {A : Type ℓ} →
  PremetricStr ℓ' A → (coordinate function derivative : A → ℂ) → Type (ℓ-max ℓ ℓ')
IsRadiuswiseUniformComplexDerivativeAlong source coordinate function derivative =
  ∀ (ε : ℚ₊) → ∃[ δ ∈ ℚ₊ ]
    (∀ x y → PremetricStr._≈[_]_ source x δ y →
      normℂ (complexDerivativeErrorAlong coordinate function (derivative x) x y) ≤ℝ
        rat (fst ε) · normℂ (coordinate y -ℂ coordinate x))

isPropIsRadiuswiseUniformComplexDerivativeAlong : ∀ {ℓ ℓ'} {A : Type ℓ}
  (source : PremetricStr ℓ' A) coordinate function derivative →
  isProp (IsRadiuswiseUniformComplexDerivativeAlong source coordinate function derivative)
isPropIsRadiuswiseUniformComplexDerivativeAlong source coordinate function derivative = isPropΠ λ _ → squash₁

uniformComplexDerivativeAlong→derivativeAlong : ∀ {ℓ ℓ'} {A : Type ℓ}
  (source : PremetricStr ℓ' A) coordinate function derivative →
  IsRadiuswiseUniformComplexDerivativeAlong source coordinate function derivative →
  IsComplexDerivativeAlong source coordinate function derivative
uniformComplexDerivativeAlong→derivativeAlong source coordinate function derivative uniform x ε =
  PT.map (λ { (δ , near) → δ , near x }) (uniform ε)

uniformComplexDerivativeAlongPrecompose : ∀ {ℓA ℓA' ℓB ℓB'} {A : Type ℓA} {B : Type ℓB}
  (source : PremetricStr ℓA' A) (target : PremetricStr ℓB' B)
  (mapping : A → B) (coordinate function derivative : B → ℂ) →
  IsRadiuswiseUniformlyContinuous source mapping target →
  IsRadiuswiseUniformComplexDerivativeAlong target coordinate function derivative →
  IsRadiuswiseUniformComplexDerivativeAlong source (coordinate ∘ mapping) (function ∘ mapping) (derivative ∘ mapping)
uniformComplexDerivativeAlongPrecompose source target mapping coordinate function derivative continuous differentiable ε =
  PT.rec squash₁ (λ { (δ , bound) → PT.map
    (λ { (η , near) → η , λ x y close → bound (mapping x) (mapping y) (near x y close) }) (continuous δ) })
    (differentiable ε)
