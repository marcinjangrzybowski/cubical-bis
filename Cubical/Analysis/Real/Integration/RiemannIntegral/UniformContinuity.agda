module Cubical.Analysis.Real.Integration.RiemannIntegral.UniformContinuity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Inverse
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open PositiveRationals.PositiveHalvesℚ using (_/2₊)
open import Cubical.Relation.Premetric.Mappings

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
open import Cubical.Analysis.Real.Order.Archimedean
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Real.Integration.UniformContinuity
open import Cubical.Analysis.Real.Integration.RiemannSum.Algebra
open import Cubical.Analysis.Real.Integration.RiemannSum.Comparison
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Base
open import Cubical.Analysis.Real.Integration.RiemannIntegral.CauchyCriterion

private opaque
  scaledComparison : ∀ f a b (bound ε δ : ℚ₊) →
    b - a <ℝ rat (fst bound) →
    (∀ (x y : ClosedInterval a b) → fst x ∼[ δ ] fst y →
      f (fst x) ∼[ ε ₊／₊ bound ] f (fst y)) →
    RiemannCauchyRadius f a b ε (δ /2₊)
  scaledComparison f a b bound ε δ length<bound close first second firstMesh secondMesh =
    absDifference<→closeness (riemannSum first f) (riemannSum second f) ε
      (≤<ℝ-trans (absℝ (riemannSum first f - riemannSum second f))
        ((b - a) · rat (fst (ε ₊／₊ bound))) (rat (fst ε))
        (riemannSumComparisonBound f (ε ₊／₊ bound) δ close first second firstMesh secondMesh)
        (subst (((b - a) · rat (fst (ε ₊／₊ bound))) <ℝ_)
          (mul-rat (fst bound) (fst (ε ₊／₊ bound)) ∙ cong rat (·／ bound ε))
          (mulPres<PosR (b - a) (rat (fst bound)) (rat (fst (ε ₊／₊ bound)))
            (positiveSlack (ε ₊／₊ bound)) length<bound)))

opaque
  radiuswiseUniformContinuityIsRiemannCauchyOn : ∀ f a b →
    IsRadiuswiseUniformlyContinuous (ClosedIntervalPremetricSpace a b .snd)
      (f ∘ fst) (ℝPremetricSpace .snd) → IsRiemannCauchyOn f a b
  radiuswiseUniformContinuityIsRiemannCauchyOn f a b continuous ε =
    PT.rec squash₁ (λ { (n , length<n) →
      PT.map (λ { (δ , close) → δ /2₊ ,
        scaledComparison f a b (naturalBound n) ε δ length<n close })
        (continuous (ε ₊／₊ naturalBound n)) })
      (∃naturalUpperBound (b - a))

  -- A supplied modulus yields one Cauchy modulus for the dyadic sums.
  -- Both existential eliminations below target the proposition of having
  -- the unique integral on an ordered interval; no choice is used.
  uniformContinuityWithIsRiemannIntegrableOn : ∀ f a b → a ≤ℝ b →
    (μ : ℚ₊ → ℚ₊) →
    IsUniformlyContinuousWith (ClosedIntervalPremetricSpace a b .snd)
      (f ∘ fst) (ℝPremetricSpace .snd) μ → IsRiemannIntegrableOn f a b
  uniformContinuityWithIsRiemannIntegrableOn f a b a≤b μ continuous =
    PT.rec (isPropIsRiemannIntegrableOn a b a≤b f)
      (λ { (n , length<n) → riemannCauchyModulusIsIntegrable f a b a≤b
        (λ ε → μ (ε ₊／₊ naturalBound n) /2₊)
        (λ ε → scaledComparison f a b (naturalBound n) ε
          (μ (ε ₊／₊ naturalBound n)) length<n
          (λ x y → IsUniformlyContinuousWith.pres≈ continuous x y (ε ₊／₊ naturalBound n))) })
      (∃naturalUpperBound (b - a))

  uniformContinuityIsRiemannIntegrableOn : ∀ f a b → a ≤ℝ b →
    isUniformlyContinuous (ClosedIntervalPremetricSpace a b .snd)
      (f ∘ fst) (ℝPremetricSpace .snd) → IsRiemannIntegrableOn f a b
  uniformContinuityIsRiemannIntegrableOn f a b a≤b =
    PT.rec (isPropIsRiemannIntegrableOn a b a≤b f)
      (λ { (μ , continuous) → uniformContinuityWithIsRiemannIntegrableOn f a b a≤b μ continuous })

  uniformContinuityIsRiemannIntegrable : ∀ f a b → a ≤ℝ b →
    isUniformlyContinuous (ℝPremetricSpace .snd) f (ℝPremetricSpace .snd) →
    IsRiemannIntegrableOn f a b
  uniformContinuityIsRiemannIntegrable f a b a≤b continuous =
    uniformContinuityIsRiemannIntegrableOn f a b a≤b
      (PT.map (λ { (μ , uc) → μ , isuniformlycontinuouswith
        (λ x y ε → IsUniformlyContinuousWith.pres≈ uc (fst x) (fst y) ε) }) continuous)

  uniformContinuityOnSubinterval : ∀ f a b x y → a ≤ℝ x → y ≤ℝ b →
    isUniformlyContinuous (ClosedIntervalPremetricSpace a b .snd)
      (f ∘ fst) (ℝPremetricSpace .snd) →
    isUniformlyContinuous (ClosedIntervalPremetricSpace x y .snd)
      (f ∘ fst) (ℝPremetricSpace .snd)
  uniformContinuityOnSubinterval f a b x y a≤x y≤b =
    PT.map (λ { (μ , uc) → μ , isuniformlycontinuouswith
      (λ p q ε → IsUniformlyContinuousWith.pres≈ uc (include p) (include q) ε) })
    where
    include : ClosedInterval x y → ClosedInterval a b
    include (z , x≤z , z≤y) = z
      , ≤ℝ-trans a x z a≤x x≤z , ≤ℝ-trans z y b z≤y y≤b
