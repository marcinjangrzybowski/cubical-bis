module Cubical.Analysis.Real.Integration.RiemannIntegral.Ordered where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Base


-- The legacy predicate quantifies over tagged partitions.  For reversed
-- endpoints there are none, so it is vacuous rather than a signed integral.
-- Bundle the endpoint order once so that uniqueness is always available.
OrderedIntegrationInterval : Type₀
OrderedIntegrationInterval = Σ[ a ∈ ℝ ] Σ[ b ∈ ℝ ] a ≤ℝ b

integrationLowerEndpoint : OrderedIntegrationInterval → ℝ
integrationLowerEndpoint = fst

integrationUpperEndpoint : OrderedIntegrationInterval → ℝ
integrationUpperEndpoint interval = fst (snd interval)

integrationEndpointsOrdered : ∀ interval →
  integrationLowerEndpoint interval ≤ℝ integrationUpperEndpoint interval
integrationEndpointsOrdered interval = snd (snd interval)

pointIntegrationInterval : ℝ → OrderedIntegrationInterval
pointIntegrationInterval a = a , a , ≤ℝ-refl a


-- These are definitionally the original predicates, so existing integral
-- witnesses and algebra laws can be used without transport.
HasRiemannIntegralOnInterval :
  (ℝ → ℝ) → OrderedIntegrationInterval → ℝ → Type₀
HasRiemannIntegralOnInterval f interval =
  HasRiemannIntegralOn f
    (integrationLowerEndpoint interval) (integrationUpperEndpoint interval)

isPropHasRiemannIntegralOnInterval : ∀ f interval value →
  isProp (HasRiemannIntegralOnInterval f interval value)
isPropHasRiemannIntegralOnInterval f interval value =
  isPropHasRiemannIntegralOn f
    (integrationLowerEndpoint interval) (integrationUpperEndpoint interval)
    value

IsRiemannIntegrableOnInterval :
  (ℝ → ℝ) → OrderedIntegrationInterval → Type₀
IsRiemannIntegrableOnInterval f interval =
  IsRiemannIntegrableOn f
    (integrationLowerEndpoint interval) (integrationUpperEndpoint interval)

integralOnInterval : ∀ interval {f} →
  IsRiemannIntegrableOnInterval f interval → ℝ
integralOnInterval interval = fst


opaque
  riemannIntegralOnIntervalUnique : ∀ interval f value value' →
    HasRiemannIntegralOnInterval f interval value →
    HasRiemannIntegralOnInterval f interval value' →
    value ≡ value'
  riemannIntegralOnIntervalUnique interval f value value' =
    riemannIntegralUnique
      (integrationLowerEndpoint interval) (integrationUpperEndpoint interval)
      (integrationEndpointsOrdered interval) f value value'

  isPropIsRiemannIntegrableOnInterval : ∀ f interval →
    isProp (IsRiemannIntegrableOnInterval f interval)
  isPropIsRiemannIntegrableOnInterval f interval =
    isPropIsRiemannIntegrableOn
      (integrationLowerEndpoint interval) (integrationUpperEndpoint interval)
      (integrationEndpointsOrdered interval) f

  integralOnIntervalIndependent : ∀ interval f
    (first second : IsRiemannIntegrableOnInterval f interval) →
    integralOnInterval interval {f} first ≡
    integralOnInterval interval {f} second
  integralOnIntervalIndependent interval f first second =
    cong fst (isPropIsRiemannIntegrableOnInterval f interval first second)
