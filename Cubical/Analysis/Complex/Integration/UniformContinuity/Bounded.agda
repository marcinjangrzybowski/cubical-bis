module Cubical.Analysis.Complex.Integration.UniformContinuity.Bounded where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition using (_+_; rat+rat)
open import Cubical.Analysis.Real.Algebra.AbsoluteValue using (absℝ)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue using (addPres≤)
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Real.Integration.UniformContinuity
open import Cubical.Analysis.Real.Integration.UniformContinuity.Bounded
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Metric
opaque
  -- Two finite real boundedness arguments suffice. Their rational bounds
  -- remain under truncation; radiuswise continuity is not made into a modulus.
  radiuswiseComplexUniformContinuityIsBoundedOn : ∀ h a b → a ≤ℝ b →
    IsRadiuswiseUniformlyContinuous (ClosedIntervalPremetricSpace a b .snd) (h ∘ fst) (ℂPremetricSpace .snd) →
    ∃[ B ∈ ℚ₊ ] (∀ t → a ≤ℝ t → t ≤ℝ b → normℂ (h t) ≤ℝ rat (fst B))
  radiuswiseComplexUniformContinuityIsBoundedOn h a b ordered continuous = PT.rec2 squash₁
    (λ { (B , realBound) (C , imaginaryBound) → ∣ B +₊ C , (λ t lo hi →
      subst (normℂ (h t) ≤ℝ_) (rat+rat (fst B) (fst C))
        (addPres≤ (absℝ (re (h t))) (rat (fst B)) (absℝ (im (h t))) (rat (fst C))
          (realBound t lo hi) (imaginaryBound t lo hi))) ∣₁ })
    (radiuswiseUniformContinuityIsBoundedOn (re ∘ h) a b ordered
      (λ ε → PT.map (λ { (δ , near) → δ , λ x y close → fst (near x y close) }) (continuous ε)))
    (radiuswiseUniformContinuityIsBoundedOn (im ∘ h) a b ordered
      (λ ε → PT.map (λ { (δ , near) → δ , λ x y close → snd (near x y close) }) (continuous ε)))

