module Cubical.Analysis.Complex.Integration.LineIntegral.RightHalfPlane where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties using (<≤ℝ-trans)
open import Cubical.Analysis.Real.Order.Strict.Slack using (positiveSlack)
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Real.Integration.UniformContinuity
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Inverse
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Domain.RightHalfPlane
open import Cubical.Analysis.Complex.Transcendental.Exponential.Base
open import Cubical.Analysis.Complex.Transcendental.Logarithm.RightHalfPlane.Base
open import Cubical.Analysis.Complex.Transcendental.Logarithm.RightHalfPlane.Uniform
open import Cubical.Analysis.Complex.Integration.Base
open import Cubical.Analysis.Complex.Integration.Path
open import Cubical.Analysis.Complex.Integration.Path.Bounds
open import Cubical.Analysis.Complex.Integration.Path.Continuity
open import Cubical.Analysis.Complex.Integration.LineIntegral.Base
open import Cubical.Analysis.Complex.Integration.LineIntegral.Along
open import Cubical.Analysis.Complex.Integration.LineIntegral.Logarithm

open import Cubical.Analysis.Complex.Integration.LineIntegral.RightHalfPlane.Path

module _ {a b : ℝ} (path : UniformComplexPath a b) (η : ℚ₊)
  (lower : ∀ t → a ≤ℝ t → t ≤ℝ b → rat (fst η) ≤ℝ re (UniformComplexPath.curve path t)) where
  private module P = UniformComplexPath path

  private
    point : ClosedInterval a b → ComplexRightHalfPlane
    point = rightHalfPlanePathPoint path η lower
    logarithm reciprocal : ℝ → ℂ
    logarithm = rightHalfPlanePathLog path η lower
    reciprocal = rightHalfPlanePathReciprocal path η lower
    logarithm-on : ∀ t (lo : a ≤ℝ t) (hi : t ≤ℝ b) → logarithm t ≡ rightHalfPlaneLog (point (t , lo , hi))
    logarithm-on = rightHalfPlanePathLog-on path η lower
    reciprocal-on : ∀ t (lo : a ≤ℝ t) (hi : t ≤ℝ b) → reciprocal t ≡ inverseℂ (P.curve t) (rightHalfPlaneNonzero (point (t , lo , hi)))
    reciprocal-on = rightHalfPlanePathReciprocal-on path η lower
    liftLaw : ∀ t → a ≤ℝ t → t ≤ℝ b → expℂ (logarithm t) ≡ P.curve t
    liftLaw = rightHalfPlanePathLiftLaw path η lower
    logarithmIsUniform : IsRadiuswiseUniformlyContinuous (ClosedIntervalPremetricSpace a b .snd) (logarithm ∘ fst) (ℂPremetricSpace .snd)
    logarithmIsUniform = rightHalfPlanePathLogIsUniform path η lower

  -- The endpoint formula for the native reciprocal along the path.
  opaque
    rightHalfPlaneReciprocalHasLineIntegral : HasComplexLineIntegralAlong reciprocal path
      (logarithm b -ℂ logarithm a)
    rightHalfPlaneReciprocalHasLineIntegral = complexHasIntegralCongOn
      (complexLineIntegrandAlong (reciprocalAlongLogarithmicLift logarithm) path)
      (complexLineIntegrandAlong reciprocal path) a b
      (logarithm b -ℂ logarithm a)
      (λ t lo hi → cong (_·ℂ P.velocity t)
        (logarithmicLiftReciprocalAgreesWithInverse path logarithm liftLaw
          logarithmIsUniform t lo hi (rightHalfPlaneNonzero (point (t , lo , hi)))
          ∙ sym (reciprocal-on t lo hi)))
      (logarithmicLiftHasComplexLineIntegral path logarithm liftLaw logarithmIsUniform)

  -- Any ambient function agreeing with the reciprocal on the image has the
  -- same integral. Its behaviour away from that image is irrelevant.
  opaque
    rightHalfPlaneInverseHasLineIntegral : (f : ℂ → ℂ) →
      (∀ t → a ≤ℝ t → t ≤ℝ b → P.curve t ·ℂ f (P.curve t) ≡ 1ℂ) →
      HasComplexLineIntegral f path (logarithm b -ℂ logarithm a)
    rightHalfPlaneInverseHasLineIntegral f inverseLaw = complexHasIntegralCongOn
      (complexLineIntegrandAlong reciprocal path) (complexLineIntegrand f path) a b
      (logarithm b -ℂ logarithm a)
      (λ t lo hi → cong (_·ℂ P.velocity t) (reciprocal-on t lo hi
        ∙ sym (inverseℂ-unique (P.curve t) (rightHalfPlaneNonzero (point (t , lo , hi)))
          (f (P.curve t)) (inverseLaw t lo hi)))) rightHalfPlaneReciprocalHasLineIntegral

  private
    endpointEquality : pathFinish path ≡ pathStart path →
      point (b , P.ordered , ≤ℝ-refl b) ≡ point (a , ≤ℝ-refl a , P.ordered)
    endpointEquality closed = Σ≡Prop (λ z → isProp<ℝ 0ℝ (re z)) closed

    closedDifference : pathFinish path ≡ pathStart path → logarithm b -ℂ logarithm a ≡ 0ℂ
    closedDifference closed = cong₂ _-ℂ_
      (logarithm-on b P.ordered (≤ℝ-refl b))
      (logarithm-on a (≤ℝ-refl a) P.ordered)
      ∙ cong (λ p → rightHalfPlaneLog p -ℂ rightHalfPlaneLog (point (a , ≤ℝ-refl a , P.ordered)))
        (endpointEquality closed)
      ∙ +ℂInvR (rightHalfPlaneLog (point (a , ≤ℝ-refl a , P.ordered)))

  closedRightHalfPlaneReciprocalHasZeroLineIntegral : pathFinish path ≡ pathStart path →
    HasComplexLineIntegralAlong reciprocal path 0ℂ
  closedRightHalfPlaneReciprocalHasZeroLineIntegral closed =
    subst (HasComplexLineIntegralAlong reciprocal path) (closedDifference closed)
      rightHalfPlaneReciprocalHasLineIntegral

  closedRightHalfPlaneInverseHasZeroLineIntegral : (f : ℂ → ℂ) →
    (∀ t → a ≤ℝ t → t ≤ℝ b → P.curve t ·ℂ f (P.curve t) ≡ 1ℂ) →
    pathFinish path ≡ pathStart path → HasComplexLineIntegral f path 0ℂ
  closedRightHalfPlaneInverseHasZeroLineIntegral f inverseLaw closed =
    subst (HasComplexLineIntegral f path) (closedDifference closed) (rightHalfPlaneInverseHasLineIntegral f inverseLaw)
