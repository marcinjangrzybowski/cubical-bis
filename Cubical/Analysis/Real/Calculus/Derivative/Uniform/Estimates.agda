module Cubical.Analysis.Real.Calculus.Derivative.Uniform.Estimates where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Inverse
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open import Cubical.Relation.Premetric.Mappings

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AdditiveGroup.Properties
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Slack
open import Cubical.Analysis.Real.Order.Strict.Multiplication
open import Cubical.Analysis.Real.Order.Metric.AbsoluteDifference
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Real.Calculus.MeanValue.Uniform
open import Cubical.Analysis.Real.Integration.Partition.Overlap
open import Cubical.Analysis.Real.Integration.UniformContinuity

opaque
  uniformDerivativeLipschitzOn : ∀ F f a b bound →
    IsRadiuswiseUniformDerivativeOn F f a b →
    (∀ z → a ≤ℝ z → z ≤ℝ b → absℝ (f z) ≤ℝ bound) →
    ∀ (x y : ClosedInterval a b) → absℝ (F (fst y) - F (fst x)) ≤ℝ bound · absℝ (fst y - fst x)
  uniformDerivativeLipschitzOn F f a b bound derivative bounded
    x@(x₀ , a≤x , x≤b) y@(y₀ , a≤y , y≤b) =
    orderCasesForBound x₀ y₀ (absℝ (F y₀ - F x₀)) (bound · absℝ (y₀ - x₀))
      (λ x≤y → subst (absℝ (F y₀ - F x₀) ≤ℝ_)
        (cong (bound ·_) (sym (absOfNonnegative (y₀ - x₀) (nonnegativeSub x₀ y₀ x≤y))))
        (radiuswiseUniformDerivativeBoundOn F f x₀ y₀ x≤y
          (radiuswiseUniformDerivativeOn→subinterval F f a b x₀ y₀ a≤x y≤b derivative) bound
          (λ z x≤z z≤y → bounded z (≤ℝ-trans a x₀ z a≤x x≤z) (≤ℝ-trans z y₀ b z≤y y≤b))))
      (λ y≤x → subst2 _≤ℝ_ (absSubComm (F x₀) (F y₀))
        (cong (bound ·_) (sym (absOfNonnegative (x₀ - y₀) (nonnegativeSub y₀ x₀ y≤x)) ∙ absSubComm x₀ y₀))
        (radiuswiseUniformDerivativeBoundOn F f y₀ x₀ y≤x
          (radiuswiseUniformDerivativeOn→subinterval F f a b y₀ x₀ a≤y x≤b derivative) bound
          (λ z y≤z z≤x → bounded z (≤ℝ-trans a y₀ z a≤y y≤z) (≤ℝ-trans z x₀ b z≤x x≤b))))

  boundedUniformDerivativeIsUniformlyContinuousOn : ∀ F f a b (bound : ℚ₊) →
    IsRadiuswiseUniformDerivativeOn F f a b →
    (∀ z → a ≤ℝ z → z ≤ℝ b → absℝ (f z) ≤ℝ rat (fst bound)) →
    isUniformlyContinuous (ClosedIntervalPremetricSpace a b .snd) (F ∘ fst) (ℝPremetricSpace .snd)
  boundedUniformDerivativeIsUniformlyContinuousOn F f a b bound derivative bounded =
    ∣ (λ ε → ε ₊／₊ bound) , isuniformlycontinuouswith (λ x y ε close → absDifference<→closeness (F (fst x)) (F (fst y)) ε
      (≤<ℝ-trans (absℝ (F (fst x) - F (fst y)))
        (rat (fst bound) · absℝ (fst x - fst y)) (rat (fst ε))
        (uniformDerivativeLipschitzOn F f a b (rat (fst bound)) derivative bounded y x)
        (subst ((rat (fst bound) · absℝ (fst x - fst y)) <ℝ_)
          (mul-rat (fst bound) (fst (ε ₊／₊ bound)) ∙ cong rat (·／ bound ε))
          (mulPres<PosL (absℝ (fst x - fst y)) (rat (fst (ε ₊／₊ bound))) (rat (fst bound))
            (positiveSlack bound) (closeness→absDifference< (fst x) (fst y) (ε ₊／₊ bound) close))))) ∣₁

  boundedUniformDerivativeGivesUniformContinuityOn : ∀ F f a b (bound : ℚ₊) →
    IsRadiuswiseUniformDerivativeOn F f a b →
    (∀ z → a ≤ℝ z → z ≤ℝ b → absℝ (f z) ≤ℝ rat (fst bound)) →
    IsRadiuswiseUniformlyContinuous (ClosedIntervalPremetricSpace a b .snd) (F ∘ fst) (ℝPremetricSpace .snd)
  boundedUniformDerivativeGivesUniformContinuityOn F f a b bound derivative bounded =
    isUniformlyContinuous→isRadiuswiseUniformlyContinuous
      (ClosedIntervalPremetricSpace a b .snd) (F ∘ fst) (ℝPremetricSpace .snd)
      (boundedUniformDerivativeIsUniformlyContinuousOn F f a b bound derivative bounded)

  boundedUniformDerivativeBoundsFunctionOn : ∀ F f a b (bound : ℚ₊) →
    IsRadiuswiseUniformDerivativeOn F f a b →
    (∀ z → a ≤ℝ z → z ≤ℝ b → absℝ (f z) ≤ℝ rat (fst bound)) →
    ∀ x → a ≤ℝ x → x ≤ℝ b → absℝ (F x) ≤ℝ absℝ (F a) + rat (fst bound) · (b - a)
  boundedUniformDerivativeBoundsFunctionOn F f a b bound derivative bounded x a≤x x≤b =
    subst (_≤ℝ absℝ (F a) + rat (fst bound) · (b - a))
      (cong absℝ (addComm (F a) (F x - F a) ∙ subAddCancel (F x) (F a)))
      (≤ℝ-trans (absℝ (F a + (F x - F a))) (absℝ (F a) + absℝ (F x - F a))
        (absℝ (F a) + rat (fst bound) · (b - a)) (absTriangle (F a) (F x - F a))
        (addPres≤L (absℝ (F x - F a)) (rat (fst bound) · (b - a)) (absℝ (F a))
          (≤ℝ-trans (absℝ (F x - F a)) (rat (fst bound) · (x - a)) (rat (fst bound) · (b - a))
            (radiuswiseUniformDerivativeBoundOn F f a x a≤x
              (radiuswiseUniformDerivativeOn→subinterval F f a b a x (≤ℝ-refl a) x≤b derivative)
              (rat (fst bound)) (λ z a≤z z≤x → bounded z a≤z (≤ℝ-trans z x b z≤x x≤b)))
            (mulPres≤L (x - a) (b - a) (rat (fst bound))
              (0≤→isNonnegative (rat (fst bound)) (<ℝ-weaken 0ℝ (rat (fst bound)) (positiveSlack bound)))
              (addPres≤R x b (- a) x≤b)))))
