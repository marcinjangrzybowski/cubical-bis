module Cubical.Analysis.Real.Integration.FundamentalTheorem.ContinuousSubstitution where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Relation.Premetric.Mappings using (isUniformlyContinuous)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Real.Calculus.MeanValue.Uniform
open import Cubical.Analysis.Real.Integration.UniformContinuity
open import Cubical.Analysis.Real.Integration.UniformContinuity.Bounded
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Base
open import Cubical.Analysis.Real.Integration.FundamentalTheorem.UniformContinuity
open import Cubical.Analysis.Real.Integration.FundamentalTheorem.Substitution

-- Uniform continuity supplies both bounds used by the substitution theorem.
-- The derivative of the change of variable needs only radiuswise continuity;
-- the outer integrand uses standard uniform continuity to construct its integral.
module ContinuousSubstitution (f G g : ℝ → ℝ) (a b c d : ℝ)
    (a≤b : a ≤ℝ b) (c≤d : c ≤ℝ d)
    (continuous : isUniformlyContinuous (ClosedIntervalPremetricSpace c d .snd) (f ∘ fst) (ℝPremetricSpace .snd))
    (innerDerivative : IsRadiuswiseUniformDerivativeOn G g a b)
    (derivativeContinuous : IsRadiuswiseUniformlyContinuous
      (ClosedIntervalPremetricSpace a b .snd) (g ∘ fst) (ℝPremetricSpace .snd))
    (imageLower : ∀ x → a ≤ℝ x → x ≤ℝ b → c ≤ℝ G x)
    (imageUpper : ∀ x → a ≤ℝ x → x ≤ℝ b → G x ≤ℝ d) where
  private
    module A = UniformlyContinuousAccumulation f c d c≤d continuous
    imageA imageB : ClosedInterval c d
    imageA = G a , imageLower a (≤ℝ-refl a) a≤b , imageUpper a (≤ℝ-refl a) a≤b
    imageB = G b , imageLower b a≤b (≤ℝ-refl b) , imageUpper b a≤b (≤ℝ-refl b)
    transformed : ℝ → ℝ
    transformed x = f (G x) · g x

  endpointIntegral : ℝ
  endpointIntegral = A.value imageB - A.value imageA

  opaque
    hasIntegral : HasRiemannIntegralOn transformed a b endpointIntegral
    hasIntegral = PT.rec2 (isPropHasRiemannIntegralOn transformed a b endpointIntegral)
      (λ { (D , outerBound) (E , innerBound) →
        UniformlyContinuousSubstitution.hasIntegral f G g a b c d a≤b c≤d D E
          continuous innerDerivative outerBound innerBound imageLower imageUpper })
      (uniformContinuityIsBoundedOn f c d c≤d continuous)
      (radiuswiseUniformContinuityIsBoundedOn g a b a≤b derivativeContinuous)

    integralEquality : G a ≤ℝ G b → ∀ sourceValue targetValue →
      HasRiemannIntegralOn transformed a b sourceValue →
      HasRiemannIntegralOn f (G a) (G b) targetValue → sourceValue ≡ targetValue
    integralEquality ordered sourceValue targetValue hasSource hasTarget =
      PT.rec2 (isSetℝ sourceValue targetValue)
        (λ { (D , outerBound) (E , innerBound) →
          UniformlyContinuousSubstitution.integralEquality f G g a b c d a≤b c≤d D E
            continuous innerDerivative outerBound innerBound imageLower imageUpper
            ordered sourceValue targetValue hasSource hasTarget })
        (uniformContinuityIsBoundedOn f c d c≤d continuous)
        (radiuswiseUniformContinuityIsBoundedOn g a b a≤b derivativeContinuous)
