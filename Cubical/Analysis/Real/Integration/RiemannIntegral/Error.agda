module Cubical.Analysis.Real.Integration.RiemannIntegral.Error where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Inverse
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Slack
open import Cubical.Analysis.Real.Order.Strict.Multiplication
open import Cubical.Analysis.Real.Order.Metric.AbsoluteDifference
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Real.Integration.Partition
open import Cubical.Analysis.Real.Integration.RiemannSum.Algebra
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Base
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Comparison

opaque
  scaledIntervalErrorSmall : ∀ a b (bound ε : ℚ₊) → b - a <ℝ rat (fst bound) →
    (b - a) · rat (fst (ε ₊／₊ bound)) <ℝ rat (fst ε)
  scaledIntervalErrorSmall a b bound ε length<bound =
    subst (((b - a) · rat (fst (ε ₊／₊ bound))) <ℝ_)
      (mul-rat (fst bound) (fst (ε ₊／₊ bound)) ∙ cong rat (·／ bound ε))
      (mulPres<PosR (b - a) (rat (fst bound)) (rat (fst (ε ₊／₊ bound)))
        (positiveSlack (ε ₊／₊ bound)) length<bound)

  riemannSumsCloseFromUniformBound : ∀ {a b} (tagged : TaggedPartition[ a , b ]) f g
    (bound ε : ℚ₊) → b - a <ℝ rat (fst bound) →
    (∀ (x : ClosedInterval a b) → f (fst x) ∼[ ε ₊／₊ bound ] g (fst x)) →
    riemannSum tagged f ∼[ ε ] riemannSum tagged g
  riemannSumsCloseFromUniformBound {a} {b} tagged f g bound ε length<bound close =
    absDifference<→closeness (riemannSum tagged f) (riemannSum tagged g) ε
      (≤<ℝ-trans (absℝ (riemannSum tagged f - riemannSum tagged g))
        ((b - a) · rat (fst (ε ₊／₊ bound))) (rat (fst ε))
        (riemannSum-differenceBoundOn tagged f g (rat (fst (ε ₊／₊ bound)))
          (λ x a≤x x≤b → <ℝ-weaken (absℝ (f x - g x)) (rat (fst (ε ₊／₊ bound)))
            (closeness→absDifference< (f x) (g x) (ε ₊／₊ bound) (close (x , a≤x , x≤b)))))
        (scaledIntervalErrorSmall a b bound ε length<bound))

  riemannIntegralsCloseFromUniformBound : ∀ a b → a ≤ℝ b → ∀ f g value value'
    (bound ε : ℚ₊) → b - a <ℝ rat (fst bound) →
    HasRiemannIntegralOn f a b value → HasRiemannIntegralOn g a b value' →
    (∀ (x : ClosedInterval a b) → f (fst x) ∼[ ε ₊／₊ bound ] g (fst x)) → value ∼[ ε ] value'
  riemannIntegralsCloseFromUniformBound a b a≤b f g value value' bound ε length<bound first second close =
    absDifference<→closeness value value' ε
      (≤<ℝ-trans (absℝ (value - value')) ((b - a) · rat (fst (ε ₊／₊ bound))) (rat (fst ε))
        (riemannIntegral-differenceBoundOn a b a≤b f g value value' (rat (fst (ε ₊／₊ bound))) first second
          (λ x a≤x x≤b → <ℝ-weaken (absℝ (f x - g x)) (rat (fst (ε ₊／₊ bound)))
            (closeness→absDifference< (f x) (g x) (ε ₊／₊ bound) (close (x , a≤x , x≤b)))))
        (scaledIntervalErrorSmall a b bound ε length<bound))
