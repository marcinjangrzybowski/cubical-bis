module Cubical.Analysis.Real.Integration.FundamentalTheorem.Substitution where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open import Cubical.Relation.Premetric.Mappings using (isUniformlyContinuous)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Real.Calculus.Derivative.Chain.Indexed
open import Cubical.Analysis.Real.Calculus.Derivative.Uniform
open import Cubical.Analysis.Real.Calculus.Derivative.Uniform.Interval
open import Cubical.Analysis.Real.Calculus.Derivative.Uniform.Estimates
open import Cubical.Analysis.Real.Calculus.Derivative.Uniform.Composition
open import Cubical.Analysis.Real.Calculus.MeanValue.Uniform
open import Cubical.Analysis.Real.Integration.UniformContinuity
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Base
open import Cubical.Analysis.Real.Integration.FundamentalTheorem.Second
open import Cubical.Analysis.Real.Integration.FundamentalTheorem.Accumulation
open import Cubical.Analysis.Real.Integration.FundamentalTheorem.UniformContinuity
open import Cubical.Analysis.Real.Integration.IntervalIntegral

-- F is a uniform antiderivative of f on the target interval. G maps the
-- source interval into it and has bounded uniform derivative g. No
-- monotonicity or injectivity of G is required for the endpoint formula.
module _ (F f G g : ℝ → ℝ) (a b c d : ℝ) (a≤b : a ≤ℝ b) (c≤d : c ≤ℝ d)
    (D E : ℚ₊)
    (outerDerivative : IsRadiuswiseUniformDerivativeOn F f c d)
    (innerDerivative : IsRadiuswiseUniformDerivativeOn G g a b)
    (outerBound : ∀ x → c ≤ℝ x → x ≤ℝ d → absℝ (f x) ≤ℝ rat (fst D))
    (innerBound : ∀ x → a ≤ℝ x → x ≤ℝ b → absℝ (g x) ≤ℝ rat (fst E))
    (imageLower : ∀ x → a ≤ℝ x → x ≤ℝ b → c ≤ℝ G x)
    (imageUpper : ∀ x → a ≤ℝ x → x ≤ℝ b → G x ≤ℝ d) where
  private
    image : ClosedInterval a b → ClosedInterval c d
    image (x , a≤x , x≤b) = G x , imageLower x a≤x x≤b , imageUpper x a≤x x≤b
    transformed : ℝ → ℝ
    transformed x = f (G x) · g x
    module J = IntervalIntegral f c d c≤d
      (uniformDerivativeIsIntegrableOnSubintervals F f c d outerDerivative)

  substitutionEndpointIntegral : ℝ
  substitutionEndpointIntegral = J.between (image (a , ≤ℝ-refl a , a≤b)) (image (b , a≤b , ≤ℝ-refl b))

  opaque
    compositeHasUniformDerivativeOn : IsRadiuswiseUniformDerivativeOn (F ∘ G) transformed a b
    compositeHasUniformDerivativeOn = uniformDerivativeAlongInterval→on (F ∘ G) transformed a b
      (chainHasUniformDerivativeAlongIndexedBounded (ClosedIntervalPremetricSpace a b .snd)
        fst (G ∘ fst) (g ∘ fst) (F ∘ G ∘ fst) (f ∘ G ∘ fst) E D
        (uniformDerivativeLipschitzOn G g a b (rat (fst E)) innerDerivative innerBound)
        (λ (x , a≤x , x≤b) → outerBound (G x) (imageLower x a≤x x≤b) (imageUpper x a≤x x≤b))
        (uniformDerivativeOn→alongInterval G g a b innerDerivative)
        (uniformDerivativeAlongPrecompose (ClosedIntervalPremetricSpace a b .snd)
          (ClosedIntervalPremetricSpace c d .snd) image fst (F ∘ fst) (f ∘ fst)
          (boundedUniformDerivativeGivesUniformContinuityOn G g a b E innerDerivative innerBound)
          (uniformDerivativeOn→alongInterval F f c d outerDerivative)))

    substitutionHasIntegral : HasRiemannIntegralOn transformed a b (F (G b) - F (G a))
    substitutionHasIntegral = fundamentalTheoremOfCalculusSecond (F ∘ G) transformed a b compositeHasUniformDerivativeOn

    substitutionOrientedHasIntegral : HasRiemannIntegralOn transformed a b substitutionEndpointIntegral
    substitutionOrientedHasIntegral = subst (HasRiemannIntegralOn transformed a b)
      (sym (J.betweenOfAntiderivative F outerDerivative (image (a , ≤ℝ-refl a , a≤b)) (image (b , a≤b , ≤ℝ-refl b))))
      substitutionHasIntegral

    substitutionIntegralEquality : G a ≤ℝ G b → ∀ sourceValue targetValue →
      HasRiemannIntegralOn transformed a b sourceValue →
      HasRiemannIntegralOn f (G a) (G b) targetValue → sourceValue ≡ targetValue
    substitutionIntegralEquality ordered sourceValue targetValue hasSource hasTarget =
      riemannIntegralUnique a b a≤b transformed sourceValue substitutionEndpointIntegral hasSource substitutionOrientedHasIntegral
      ∙ J.betweenAgreesWithIntegral (image (a , ≤ℝ-refl a , a≤b)) (image (b , a≤b , ≤ℝ-refl b))
        ordered targetValue hasTarget


-- FTC constructs the outer antiderivative from uniform continuity. The
-- caller supplies no primitive and no transformed-integrability witness.
module UniformlyContinuousSubstitution (f G g : ℝ → ℝ) (a b c d : ℝ)
    (a≤b : a ≤ℝ b) (c≤d : c ≤ℝ d) (D E : ℚ₊)
    (continuous : isUniformlyContinuous (ClosedIntervalPremetricSpace c d .snd) (f ∘ fst) (ℝPremetricSpace .snd))
    (innerDerivative : IsRadiuswiseUniformDerivativeOn G g a b)
    (outerBound : ∀ x → c ≤ℝ x → x ≤ℝ d → absℝ (f x) ≤ℝ rat (fst D))
    (innerBound : ∀ x → a ≤ℝ x → x ≤ℝ b → absℝ (g x) ≤ℝ rat (fst E))
    (imageLower : ∀ x → a ≤ℝ x → x ≤ℝ b → c ≤ℝ G x)
    (imageUpper : ∀ x → a ≤ℝ x → x ≤ℝ b → G x ≤ℝ d) where
  private
    module A = UniformlyContinuousAccumulation f c d c≤d continuous
    imageA imageB : ClosedInterval c d
    imageA = G a , imageLower a (≤ℝ-refl a) a≤b , imageUpper a (≤ℝ-refl a) a≤b
    imageB = G b , imageLower b a≤b (≤ℝ-refl b) , imageUpper b a≤b (≤ℝ-refl b)

  endpointIntegral : ℝ
  endpointIntegral = A.value imageB - A.value imageA

  opaque
    hasIntegral : HasRiemannIntegralOn (λ x → f (G x) · g x) a b endpointIntegral
    hasIntegral = subst (HasRiemannIntegralOn (λ x → f (G x) · g x) a b)
      (cong₂ _-_ (A.clampedValueAgrees imageB) (A.clampedValueAgrees imageA))
      (substitutionHasIntegral A.clampedValue f G g a b c d a≤b c≤d D E
        A.clampedValueHasUniformDerivativeOn innerDerivative outerBound innerBound imageLower imageUpper)

    integralEquality : G a ≤ℝ G b → ∀ sourceValue targetValue →
      HasRiemannIntegralOn (λ x → f (G x) · g x) a b sourceValue →
      HasRiemannIntegralOn f (G a) (G b) targetValue → sourceValue ≡ targetValue
    integralEquality = substitutionIntegralEquality A.clampedValue f G g a b c d a≤b c≤d D E
      A.clampedValueHasUniformDerivativeOn innerDerivative outerBound innerBound imageLower imageUpper
