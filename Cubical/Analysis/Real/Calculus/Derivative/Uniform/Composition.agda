module Cubical.Analysis.Real.Calculus.Derivative.Uniform.Composition where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Relation.Premetric.Base
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Calculus.Derivative.Uniform
open import Cubical.Analysis.Real.Integration.UniformContinuity

uniformDerivativeAlongPrecompose : ∀ {ℓA ℓA' ℓB ℓB'} {A : Type ℓA} {B : Type ℓB}
  (source : PremetricStr ℓA' A) (target : PremetricStr ℓB' B)
  (mapping : A → B) (coordinate function derivative : B → ℝ) →
  IsRadiuswiseUniformlyContinuous source mapping target →
  IsRadiuswiseUniformDerivativeAlong target coordinate function derivative →
  IsRadiuswiseUniformDerivativeAlong source (coordinate ∘ mapping) (function ∘ mapping) (derivative ∘ mapping)
uniformDerivativeAlongPrecompose source target mapping coordinate function derivative continuous differentiable ε =
  PT.rec squash₁ (λ { (δ , bound) → PT.map
    (λ { (η , near) → η , λ x y close → bound (mapping x) (mapping y) (near x y close) }) (continuous δ) })
    (differentiable ε)
