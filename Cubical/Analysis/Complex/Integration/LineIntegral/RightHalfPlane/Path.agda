module Cubical.Analysis.Complex.Integration.LineIntegral.RightHalfPlane.Path where

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
open import Cubical.Analysis.Complex.Integration.Path
open import Cubical.Analysis.Complex.Integration.Path.Bounds
open import Cubical.Analysis.Complex.Integration.Path.Continuity

-- The logarithmic lift is constructed here. The positive rational lower
-- bound is explicit geometric data; no compactness-to-modulus selection is
-- assumed. Clamping only supplies values outside the integration interval.
module _ {a b : ℝ} (path : UniformComplexPath a b) (η : ℚ₊)
  (lower : ∀ t → a ≤ℝ t → t ≤ℝ b → rat (fst η) ≤ℝ re (UniformComplexPath.curve path t)) where
  private module P = UniformComplexPath path

  private
    opaque
      curvePositive : ∀ t → a ≤ℝ t → t ≤ℝ b → 0ℝ <ℝ re (P.curve t)
      curvePositive t lo hi = <≤ℝ-trans 0ℝ (rat (fst η)) (re (P.curve t)) (positiveSlack η) (lower t lo hi)

  rightHalfPlanePathPoint : ClosedInterval a b → ComplexRightHalfPlane
  rightHalfPlanePathPoint (t , lo , hi) = P.curve t , curvePositive t lo hi

  private
    clampedPoint : ℝ → ComplexRightHalfPlane
    clampedPoint = rightHalfPlanePathPoint ∘ fst (clampIntervalRetractionNE a b P.ordered)

    clampedPoint-on : ∀ (x : ClosedInterval a b) → clampedPoint (fst x) ≡ rightHalfPlanePathPoint x
    clampedPoint-on x = Σ≡Prop (λ z → isProp<ℝ 0ℝ (re z))
      (cong P.curve (clampIntervalFix a b (fst x) (fst (snd x)) (snd (snd x))))

  rightHalfPlanePathLog : ℝ → ℂ
  rightHalfPlanePathLog = rightHalfPlaneLog ∘ clampedPoint

  rightHalfPlanePathReciprocal : ℝ → ℂ
  rightHalfPlanePathReciprocal = rightHalfPlaneReciprocal ∘ clampedPoint

  rightHalfPlanePathLog-on : ∀ t (lo : a ≤ℝ t) (hi : t ≤ℝ b) → rightHalfPlanePathLog t ≡ rightHalfPlaneLog (rightHalfPlanePathPoint (t , lo , hi))
  rightHalfPlanePathLog-on t lo hi = cong rightHalfPlaneLog (clampedPoint-on (t , lo , hi))

  rightHalfPlanePathReciprocal-on : ∀ t (lo : a ≤ℝ t) (hi : t ≤ℝ b) → rightHalfPlanePathReciprocal t ≡
    inverseℂ (P.curve t) (rightHalfPlaneNonzero (rightHalfPlanePathPoint (t , lo , hi)))
  rightHalfPlanePathReciprocal-on t lo hi = cong rightHalfPlaneReciprocal (clampedPoint-on (t , lo , hi))

  rightHalfPlanePathLiftLaw : ∀ t → a ≤ℝ t → t ≤ℝ b → expℂ (rightHalfPlanePathLog t) ≡ P.curve t
  rightHalfPlanePathLiftLaw t lo hi = cong expℂ (rightHalfPlanePathLog-on t lo hi)
    ∙ expℂ-rightHalfPlaneLog (rightHalfPlanePathPoint (t , lo , hi))

  rightHalfPlanePathLogIsUniform : IsRadiuswiseUniformlyContinuous (ClosedIntervalPremetricSpace a b .snd)
    (rightHalfPlanePathLog ∘ fst) (ℂPremetricSpace .snd)
  rightHalfPlanePathLogIsUniform = subst
    (λ f → IsRadiuswiseUniformlyContinuous (ClosedIntervalPremetricSpace a b .snd) f (ℂPremetricSpace .snd))
    (sym (funExt (λ (t , lo , hi) → rightHalfPlanePathLog-on t lo hi)))
    (rightHalfPlaneLogUniformAlong (ClosedIntervalPremetricSpace a b .snd) rightHalfPlanePathPoint η
      (pathImageNormBound path) (λ (t , lo , hi) → lower t lo hi)
      (λ (t , lo , hi) → pathImageIsBounded path t lo hi) (pathIsRadiuswiseUniformlyContinuous path))

