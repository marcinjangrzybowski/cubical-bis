module Cubical.Analysis.Complex.Integration.Substitution where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Real.Integration.UniformContinuity
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Integration.Base
open import Cubical.Analysis.Complex.Integration.FundamentalTheorem
open import Cubical.Analysis.Complex.Integration.UniformContinuity
open import Cubical.Analysis.Complex.Integration.Path
open import Cubical.Analysis.Complex.Integration.Path.Reparameterization
open import Cubical.Analysis.Complex.Integration.UniformContinuity.Bounded
import Cubical.Analysis.Complex.Modulus.DistanceAlgebra as Algebra

private module C = Algebra.DistanceAlgebra ℂCommRing

-- The real first FTC constructs the primitive. Thus substitution below
-- requires no complex primitive, no injectivity and no monotonicity.
module ComplexSubstitution {a b c d : ℝ} (h : ℝ → ℂ) (ordered : c ≤ℝ d)
  (continuous : isUniformlyContinuous (ClosedIntervalPremetricSpace c d .snd) (h ∘ fst) (ℂPremetricSpace .snd))
  (change : UniformParameterChange a b)
  (imageLower : ∀ t → a ≤ℝ t → t ≤ℝ b → c ≤ℝ UniformParameterChange.curve change t)
  (imageUpper : ∀ t → a ≤ℝ t → t ≤ℝ b → UniformParameterChange.curve change t ≤ℝ d) where
  private
    module T = UniformParameterChange change
    module A = UniformlyContinuousComplexAccumulation h c d ordered continuous

    primitivePath : ∀ (B : ℚ₊) → (∀ t → c ≤ℝ t → t ≤ℝ d → normℂ (h t) ≤ℝ rat (fst B)) → UniformComplexPath c d
    primitivePath B bounded .UniformComplexPath.ordered = ordered
    primitivePath B bounded .UniformComplexPath.curve = A.clampedValue
    primitivePath B bounded .UniformComplexPath.velocity = h
    primitivePath B bounded .UniformComplexPath.differentiable = A.hasUniformDerivative
    primitivePath B bounded .UniformComplexPath.speedBound = B
    primitivePath B bounded .UniformComplexPath.boundedSpeed = bounded

  transformed : ℝ → ℂ
  transformed t = h (T.curve t) ·ℂ fromℝ (T.velocity t)

  endpointIntegral : ℂ
  endpointIntegral = A.clampedValue (T.curve b) -ℂ A.clampedValue (T.curve a)

  opaque
    hasIntegral : HasComplexRiemannIntegralOn transformed a b endpointIntegral
    hasIntegral = PT.rec (isPropHasComplexRiemannIntegralOn transformed a b endpointIntegral)
      (λ { (B , bound) → complexFundamentalTheoremOfCalculus (A.clampedValue ∘ T.curve) transformed a b
        (reparameterizedCurveDerivative (primitivePath B bound) change imageLower imageUpper) })
      (radiuswiseComplexUniformContinuityIsBoundedOn h c d ordered
        (isUniformlyContinuous→isRadiuswiseUniformlyContinuous (ClosedIntervalPremetricSpace c d .snd) (h ∘ fst)
          (ℂPremetricSpace .snd) continuous))

  hasIntegralSameEndpoints : T.curve a ≡ c → T.curve b ≡ d → ∀ value →
    HasComplexRiemannIntegralOn h c d value → HasComplexRiemannIntegralOn transformed a b value
  hasIntegralSameEndpoints start finish value proof = subst (HasComplexRiemannIntegralOn transformed a b)
    (cong₂ _-ℂ_ (cong A.clampedValue finish) (cong A.clampedValue start) ∙ sym (A.integralValue value proof)) hasIntegral

  hasIntegralSwappedEndpoints : T.curve a ≡ d → T.curve b ≡ c → ∀ value →
    HasComplexRiemannIntegralOn h c d value → HasComplexRiemannIntegralOn transformed a b (-ℂ value)
  hasIntegralSwappedEndpoints start finish value proof = subst (HasComplexRiemannIntegralOn transformed a b)
    (cong₂ _-ℂ_ (cong A.clampedValue finish) (cong A.clampedValue start)
      ∙ C.difference-opposite (A.clampedValue c) (A.clampedValue d)
      ∙ cong -ℂ_ (sym (A.integralValue value proof))) hasIntegral
