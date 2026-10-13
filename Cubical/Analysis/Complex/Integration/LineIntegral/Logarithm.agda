module Cubical.Analysis.Complex.Integration.LineIntegral.Logarithm where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Multiplication using (_·_)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Real.Integration.UniformContinuity
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Inverse
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Calculus.Derivative.Uniform.Chain
open import Cubical.Analysis.Complex.Calculus.Derivative.Uniform.RealParameter
open import Cubical.Analysis.Complex.Transcendental.Exponential.Base
open import Cubical.Analysis.Complex.Transcendental.Exponential.Properties
open import Cubical.Analysis.Complex.Transcendental.Exponential.Uniform.Bounds
open import Cubical.Analysis.Complex.Transcendental.Logarithm.Uniform
open import Cubical.Analysis.Complex.Integration.Base
open import Cubical.Analysis.Complex.Integration.Curve
open import Cubical.Analysis.Complex.Integration.Path
open import Cubical.Analysis.Complex.Integration.Path.Continuity
open import Cubical.Analysis.Complex.Integration.FundamentalTheorem
open import Cubical.Analysis.Complex.Integration.UniformContinuity.Bounded
open import Cubical.Analysis.Complex.Integration.LineIntegral.Base
open import Cubical.Analysis.Complex.Integration.LineIntegral.Along

reciprocalAlongLogarithmicLift : (ℝ → ℂ) → ℝ → ℂ
reciprocalAlongLogarithmicLift logarithm t = expℂ (-ℂ logarithm t)

module _ {a b : ℝ} (path : UniformComplexPath a b) (logarithm : ℝ → ℂ)
  (liftLaw : ∀ t → a ≤ℝ t → t ≤ℝ b → expℂ (logarithm t) ≡ UniformComplexPath.curve path t)
  (continuous : IsRadiuswiseUniformlyContinuous (ClosedIntervalPremetricSpace a b .snd) (logarithm ∘ fst) (ℂPremetricSpace .snd)) where
  private
    module P = UniformComplexPath path
    reciprocal : ℝ → ℂ
    reciprocal = reciprocalAlongLogarithmicLift logarithm

  logarithmicLiftReciprocalLaw : ∀ t → a ≤ℝ t → t ≤ℝ b → P.curve t ·ℂ reciprocal t ≡ 1ℂ
  logarithmicLiftReciprocalLaw t lo hi = subst (λ z → z ·ℂ reciprocal t ≡ 1ℂ) (liftLaw t lo hi) (expℂ-neg-inverse (logarithm t))

  logarithmicLiftReciprocalAgreesWithInverse : ∀ t → a ≤ℝ t → t ≤ℝ b → (nonzero : ComplexNonzero (P.curve t)) →
    reciprocal t ≡ inverseℂ (P.curve t) nonzero
  logarithmicLiftReciprocalAgreesWithInverse t lo hi nonzero =
    inverseℂ-unique (P.curve t) nonzero (reciprocal t) (logarithmicLiftReciprocalLaw t lo hi)

  private
    opaque
      boundedLiftDerivative : ∀ (B C : ℚ₊) →
        (∀ t → a ≤ℝ t → t ≤ℝ b → normℂ (P.curve t) ≤ℝ rat (fst B)) →
        (∀ t → a ≤ℝ t → t ≤ℝ b → normℂ (reciprocal t) ≤ℝ rat (fst C)) →
        IsUniformComplexCurveDerivativeOn logarithm (complexLineIntegrandAlong reciprocal path) a b
      boundedLiftDerivative B C curveBound inverseBound = uniformCurveDerivativeAlong→on logarithm
        (complexLineIntegrandAlong reciprocal path) a b
        (chainHasUniformComplexDerivativeAlongIndexedBounded (ClosedIntervalPremetricSpace a b .snd)
          (fromℝ ∘ fst) (P.curve ∘ fst) (P.velocity ∘ fst) (logarithm ∘ fst) (reciprocal ∘ fst)
          (P.speedBound +₊ P.speedBound) C
          (λ x y → subst (normℂ (P.curve (fst y) -ℂ P.curve (fst x)) ≤ℝ_)
            (sym (cong (rat (fst (P.speedBound +₊ P.speedBound)) ·_) (realParameterDisplacementNorm fst x y)))
            (uniformComplexCurveLipschitzOn P.curve P.velocity a b P.speedBound P.differentiable P.boundedSpeed x y))
          (λ (t , lo , hi) → inverseBound t lo hi)
          (uniformCurveDerivativeOn→along P.curve P.velocity a b P.differentiable)
          (logarithmBranchHasUniformDerivativeAlong (ClosedIntervalPremetricSpace a b .snd)
            (P.curve ∘ fst) (logarithm ∘ fst) (reciprocal ∘ fst) B C
            (λ (t , lo , hi) → liftLaw t lo hi)
            (λ (t , lo , hi) → ·ℂComm (reciprocal t) (P.curve t) ∙ logarithmicLiftReciprocalLaw t lo hi)
            (λ (t , lo , hi) → curveBound t lo hi) (λ (t , lo , hi) → inverseBound t lo hi) continuous))

  -- The bounds needed for inverse differentiation are derived from the
  -- two continuous curves. Only three individual truncated bounds are used.
  -- This theorem does not select a logarithm: its lift is explicit input.
  opaque
    logarithmicLiftHasComplexLineIntegral : HasComplexLineIntegralAlong reciprocal path (logarithm b -ℂ logarithm a)
    logarithmicLiftHasComplexLineIntegral = PT.rec2 resultIsProp
      (λ { (B , curveBound) (R , logBound) → PT.rec resultIsProp
        (λ { (C , expBound) → complexFundamentalTheoremOfCalculus logarithm (complexLineIntegrandAlong reciprocal path) a b
          (boundedLiftDerivative B C curveBound
            (λ t lo hi → expBound (-ℂ logarithm t)
              (subst (_≤ℝ rat (fst R)) (sym (normℂ-neg (logarithm t))) (logBound t lo hi)))) })
        (expℂRationalBoundOnBall (rat (fst R))) })
      (radiuswiseComplexUniformContinuityIsBoundedOn P.curve a b P.ordered (pathIsRadiuswiseUniformlyContinuous path))
      (radiuswiseComplexUniformContinuityIsBoundedOn logarithm a b P.ordered continuous)
      where
      resultIsProp : isProp (HasComplexLineIntegralAlong reciprocal path (logarithm b -ℂ logarithm a))
      resultIsProp = isPropHasComplexRiemannIntegralOn (complexLineIntegrandAlong reciprocal path) a b (logarithm b -ℂ logarithm a)

-- A single-valued local branch gives a primitive for any supplied reciprocal
-- integrand on the path. No branch or reciprocal is required off that image.
logarithmBranchHasComplexLineIntegral : ∀ {a b} (path : UniformComplexPath a b) (F f : ℂ → ℂ) →
  (∀ t → a ≤ℝ t → t ≤ℝ b → expℂ (F (UniformComplexPath.curve path t)) ≡ UniformComplexPath.curve path t) →
  (∀ t → a ≤ℝ t → t ≤ℝ b → UniformComplexPath.curve path t ·ℂ f (UniformComplexPath.curve path t) ≡ 1ℂ) →
  IsRadiuswiseUniformlyContinuous (ClosedIntervalPremetricSpace a b .snd)
    (F ∘ UniformComplexPath.curve path ∘ fst) (ℂPremetricSpace .snd) →
  HasComplexLineIntegral f path (F (pathFinish path) -ℂ F (pathStart path))
logarithmBranchHasComplexLineIntegral {a} {b} path F f branchLaw inverseLaw continuous =
  complexHasIntegralCongOn (complexLineIntegrandAlong (reciprocalAlongLogarithmicLift logarithm) path)
    (complexLineIntegrand f path) a b (F (pathFinish path) -ℂ F (pathStart path))
    (λ t lo hi → cong (_·ℂ P.velocity t) (agree t lo hi))
    (logarithmicLiftHasComplexLineIntegral path logarithm branchLaw continuous)
  where
  module P = UniformComplexPath path
  logarithm : ℝ → ℂ
  logarithm = F ∘ P.curve
  agree : ∀ t → a ≤ℝ t → t ≤ℝ b → reciprocalAlongLogarithmicLift logarithm t ≡ f (P.curve t)
  agree t lo hi = logarithmicLiftReciprocalAgreesWithInverse path logarithm branchLaw continuous t lo hi nonzero
    ∙ sym (inverseℂ-unique (P.curve t) nonzero (f (P.curve t)) (inverseLaw t lo hi))
    where
    nonzero : ComplexNonzero (P.curve t)
    nonzero = subst ComplexNonzero (branchLaw t lo hi) (expℂ-nonzero (logarithm t))

closedLogarithmBranchHasZeroLineIntegral : ∀ {a b} (path : UniformComplexPath a b) (F f : ℂ → ℂ) →
  (∀ t → a ≤ℝ t → t ≤ℝ b → expℂ (F (UniformComplexPath.curve path t)) ≡ UniformComplexPath.curve path t) →
  (∀ t → a ≤ℝ t → t ≤ℝ b → UniformComplexPath.curve path t ·ℂ f (UniformComplexPath.curve path t) ≡ 1ℂ) →
  IsRadiuswiseUniformlyContinuous (ClosedIntervalPremetricSpace a b .snd)
    (F ∘ UniformComplexPath.curve path ∘ fst) (ℂPremetricSpace .snd) →
  pathFinish path ≡ pathStart path → HasComplexLineIntegral f path 0ℂ
closedLogarithmBranchHasZeroLineIntegral path F f branchLaw inverseLaw continuous closed =
  subst (HasComplexLineIntegral f path) (cong (λ z → F z -ℂ F (pathStart path)) closed ∙ +ℂInvR (F (pathStart path)))
    (logarithmBranchHasComplexLineIntegral path F f branchLaw inverseLaw continuous)
