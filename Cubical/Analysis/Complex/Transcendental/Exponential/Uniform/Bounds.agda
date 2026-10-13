module Cubical.Analysis.Complex.Transcendental.Exponential.Uniform.Bounds where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open import Cubical.Relation.Premetric.Base
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition using (_+_)
open import Cubical.Analysis.Real.Algebra.AbsoluteValue using (absℝ)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue using (leAbs; addPres≤)
open import Cubical.Analysis.Real.Order.Strict.Properties using (<ℝ-weaken)
open import Cubical.Analysis.Real.Order.Archimedean
open import Cubical.Analysis.Real.Integration.UniformContinuity
open import Cubical.Analysis.Real.Functions.Exponential using (expℝ)
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Order using (exponentialEntireValue-preserves≤)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Modulus.Base
open import Cubical.Analysis.Complex.Modulus.Bounds
open import Cubical.Analysis.Complex.Calculus.Derivative.Uniform
open import Cubical.Analysis.Complex.Transcendental.Exponential.Base
open import Cubical.Analysis.Complex.Transcendental.Exponential.Properties
open import Cubical.Analysis.Complex.Transcendental.Exponential.Uniform

opaque
  expℂNormBoundOnBall : ∀ radius z → normℂ z ≤ℝ radius → normℂ (expℂ z) ≤ℝ expℝ radius + expℝ radius
  expℂNormBoundOnBall radius z bound =
    ≤ℝ-trans (normℂ (expℂ z)) (expℝ (re z) + expℝ (re z)) (expℝ radius + expℝ radius)
      (subst (normℂ (expℂ z) ≤ℝ_) (cong₂ _+_ (modulusℂ-exp z) (modulusℂ-exp z)) (normℂ≤twiceModulusℂ (expℂ z)))
      (addPres≤ (expℝ (re z)) (expℝ radius) (expℝ (re z)) (expℝ radius) monotone monotone)
    where
    monotone : expℝ (re z) ≤ℝ expℝ radius
    monotone = exponentialEntireValue-preserves≤ (re z) radius
      (≤ℝ-trans (re z) (absℝ (re z)) radius (leAbs (re z))
        (≤ℝ-trans (absℝ (re z)) (normℂ z) radius (reAbs≤normℂ z) bound))

  expℂRationalBoundOnBall : ∀ radius → ∃[ B ∈ ℚ₊ ] (∀ z → normℂ z ≤ℝ radius → normℂ (expℂ z) ≤ℝ rat (fst B))
  expℂRationalBoundOnBall radius = PT.map (λ { (n , bounded) → naturalBound n , λ z inside →
    ≤ℝ-trans (normℂ (expℂ z)) (expℝ radius + expℝ radius) (rat (naturalRational n))
      (expℂNormBoundOnBall radius z inside) (<ℝ-weaken (expℝ radius + expℝ radius) (rat (naturalRational n)) bounded) })
    (∃naturalUpperBound (expℝ radius + expℝ radius))

  expℂHasUniformDerivativeAlongNormBounded : ∀ {ℓ ℓ'} {A : Type ℓ} (source : PremetricStr ℓ' A)
    (coordinate : A → ℂ) radius → (∀ x → normℂ (coordinate x) ≤ℝ radius) →
    IsRadiuswiseUniformlyContinuous source coordinate (ℂPremetricSpace .snd) →
    IsRadiuswiseUniformComplexDerivativeAlong source coordinate (expℂ ∘ coordinate) (expℂ ∘ coordinate)
  expℂHasUniformDerivativeAlongNormBounded source coordinate radius bounded continuous =
    PT.rec (isPropIsRadiuswiseUniformComplexDerivativeAlong source coordinate (expℂ ∘ coordinate) (expℂ ∘ coordinate))
      (λ { (B , bound) → expℂHasUniformDerivativeAlongBounded source coordinate B (λ x → bound (coordinate x) (bounded x)) continuous })
      (expℂRationalBoundOnBall radius)
