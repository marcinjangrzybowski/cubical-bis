module Cubical.Analysis.Real.Integration.FundamentalTheorem.IntegrationByParts where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Archimedean
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Real.Calculus.Derivative.Product
open import Cubical.Analysis.Real.Calculus.Derivative.Uniform.Interval
open import Cubical.Analysis.Real.Calculus.Derivative.Uniform.Estimates
open import Cubical.Analysis.Real.Calculus.MeanValue.Uniform
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Base
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Extensionality
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Laws.Add
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Laws.Sub
open import Cubical.Analysis.Real.Integration.FundamentalTheorem.Second

module _ (F G f g : ℝ → ℝ) (a b : ℝ) (D E : ℚ₊)
    (FDerivative : IsRadiuswiseUniformDerivativeOn F f a b)
    (GDerivative : IsRadiuswiseUniformDerivativeOn G g a b)
    (fBound : ∀ x → a ≤ℝ x → x ≤ℝ b → absℝ (f x) ≤ℝ rat (fst D))
    (gBound : ∀ x → a ≤ℝ x → x ≤ℝ b → absℝ (g x) ≤ℝ rat (fst E)) where
  private
    boundary : ℝ
    boundary = F b · G b - F a · G a
    left right total : ℝ → ℝ
    left x = f x · G x
    right x = F x · g x
    total x = left x + right x

  opaque
    productHasUniformDerivativeOn : IsRadiuswiseUniformDerivativeOn (λ x → F x · G x) total a b
    productHasUniformDerivativeOn =
      PT.rec (isPropIsRadiuswiseUniformDerivativeOn (λ x → F x · G x) total a b)
        (λ { (nF , Fsmall) →
          PT.rec (isPropIsRadiuswiseUniformDerivativeOn (λ x → F x · G x) total a b)
            (λ { (nG , Gsmall) → uniformDerivativeAlongInterval→on (λ x → F x · G x) total a b
              (mulHasUniformDerivativeAlongBounded (ClosedIntervalPremetricSpace a b .snd)
                fst (F ∘ fst) (G ∘ fst) (f ∘ fst) (g ∘ fst) (naturalBound nF) (naturalBound nG) D
                (λ (x , a≤x , x≤b) → ≤ℝ-trans (absℝ (F x)) Fbound (rat (naturalRational nF))
                  (boundedUniformDerivativeBoundsFunctionOn F f a b D FDerivative fBound x a≤x x≤b)
                  (<ℝ-weaken Fbound (rat (naturalRational nF)) Fsmall))
                (λ (x , a≤x , x≤b) → ≤ℝ-trans (absℝ (G x)) Gbound (rat (naturalRational nG))
                  (boundedUniformDerivativeBoundsFunctionOn G g a b E GDerivative gBound x a≤x x≤b)
                  (<ℝ-weaken Gbound (rat (naturalRational nG)) Gsmall))
                (λ (x , a≤x , x≤b) → fBound x a≤x x≤b)
                (boundedUniformDerivativeGivesUniformContinuityOn G g a b E GDerivative gBound)
                (uniformDerivativeOn→alongInterval F f a b FDerivative)
                (uniformDerivativeOn→alongInterval G g a b GDerivative)) })
            (∃naturalUpperBound Gbound) }) (∃naturalUpperBound Fbound)
      where
      Fbound Gbound : ℝ
      Fbound = absℝ (F a) + rat (fst D) · (b - a)
      Gbound = absℝ (G a) + rat (fst E) · (b - a)

    integrationByPartsSumHasIntegral : HasRiemannIntegralOn total a b boundary
    integrationByPartsSumHasIntegral =
      fundamentalTheoremOfCalculusSecond (λ x → F x · G x) total a b productHasUniformDerivativeOn

    -- Either product's integrability supplies the other's, by subtracting
    -- its integral from the integral of the product derivative.
    integrationByPartsFromRight : ∀ value → HasRiemannIntegralOn right a b value →
      HasRiemannIntegralOn left a b (boundary - value)
    integrationByPartsFromRight value hasValue =
      hasRiemannIntegral-congOn (λ x → total x - right x) left a b (boundary - value)
        (λ x _ _ → sym (addAssoc (left x) (right x) (- right x))
          ∙ cong (left x +_) (subSelf (right x)) ∙ addIdR (left x))
        (subHasRiemannIntegral total right boundary value integrationByPartsSumHasIntegral hasValue)

    integrationByPartsFromLeft : ∀ value → HasRiemannIntegralOn left a b value →
      HasRiemannIntegralOn right a b (boundary - value)
    integrationByPartsFromLeft value hasValue =
      hasRiemannIntegral-congOn (λ x → total x - left x) right a b (boundary - value)
        (λ x _ _ → cong (_- left x) (addComm (left x) (right x))
          ∙ sym (addAssoc (right x) (left x) (- left x))
          ∙ cong (right x +_) (subSelf (left x)) ∙ addIdR (right x))
        (subHasRiemannIntegral total left boundary value integrationByPartsSumHasIntegral hasValue)

    integrationByParts : a ≤ℝ b → ∀ leftValue rightValue →
      HasRiemannIntegralOn left a b leftValue → HasRiemannIntegralOn right a b rightValue →
      leftValue ≡ boundary - rightValue
    integrationByParts a≤b leftValue rightValue hasLeft hasRight =
      riemannIntegralUnique a b a≤b left leftValue (boundary - rightValue)
        hasLeft (integrationByPartsFromRight rightValue hasRight)

    integrationByPartsSum : a ≤ℝ b → ∀ leftValue rightValue →
      HasRiemannIntegralOn left a b leftValue → HasRiemannIntegralOn right a b rightValue →
      leftValue + rightValue ≡ boundary
    integrationByPartsSum a≤b leftValue rightValue hasLeft hasRight =
      riemannIntegralUnique a b a≤b total (leftValue + rightValue) boundary
        (addHasRiemannIntegral left right leftValue rightValue hasLeft hasRight)
        integrationByPartsSumHasIntegral

    integrationByPartsLeftIntegrable : IsRiemannIntegrableOn right a b → IsRiemannIntegrableOn left a b
    integrationByPartsLeftIntegrable (value , hasValue) = boundary - value , integrationByPartsFromRight value hasValue

    integrationByPartsRightIntegrable : IsRiemannIntegrableOn left a b → IsRiemannIntegrableOn right a b
    integrationByPartsRightIntegrable (value , hasValue) = boundary - value , integrationByPartsFromLeft value hasValue
