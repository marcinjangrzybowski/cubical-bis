module Cubical.Analysis.Real.Integration.IntervalIntegral where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊; _·₊_)
open import Cubical.Relation.Premetric.Mappings

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AdditiveGroup.Properties
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Slack
open import Cubical.Analysis.Real.Order.Strict.Multiplication
open import Cubical.Analysis.Real.Order.Metric.AbsoluteDifference
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Real.Calculus.Derivative.Base
open import Cubical.Analysis.Real.Calculus.Derivative.Basic
open import Cubical.Analysis.Real.Calculus.Derivative.Algebra
open import Cubical.Analysis.Real.Calculus.MeanValue.Uniform
open import Cubical.Analysis.Real.Integration.Partition.Overlap
open import Cubical.Analysis.Real.Integration.UniformContinuity.Bounded
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Base
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Comparison
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Extensionality
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Laws.Concatenation
open import Cubical.Analysis.Real.Integration.FundamentalTheorem.Algebra
open import Cubical.Analysis.Real.Integration.FundamentalTheorem.IntegralBound
open import Cubical.Analysis.Real.Integration.FundamentalTheorem.Accumulation
open import Cubical.Analysis.Real.Integration.FundamentalTheorem.UniformContinuity

-- Oriented integrals between arbitrary points of one interval. Defining
-- them as differences of a primitive avoids deciding which endpoint is
-- larger. The ordered case agrees with the semantic tagged integral.
module IntervalIntegral (f : ℝ → ℝ) (a b : ℝ) (a≤b : a ≤ℝ b)
    (integrable : IsIntegrableOnSubintervals f a b) where
  private
    module A = Accumulation f a b a≤b integrable
  open A public using (value; hasValue)

  between : ClosedInterval a b → ClosedInterval a b → ℝ
  between x y = value y - value x

  opaque
    valueAtLowerEndpoint : value (a , ≤ℝ-refl a , a≤b) ≡ 0ℝ
    valueAtLowerEndpoint = riemannIntegralOnPointIsZero f a
      (value (a , ≤ℝ-refl a , a≤b)) (hasValue (a , ≤ℝ-refl a , a≤b))

    betweenRefl : ∀ x → between x x ≡ 0ℝ
    betweenRefl x = subSelf (value x)

    betweenReverse : ∀ x y → between y x ≡ - between x y
    betweenReverse x y = sym (negSub (value y) (value x))

    betweenAdditive : ∀ x y z → between x y + between y z ≡ between x z
    betweenAdditive x y z = addComm (between x y) (between y z)
      ∙ splitDifference (value x) (value z) (value y)

    betweenBasepointIndependent : ∀ base x y → between base y - between base x ≡ between x y
    betweenBasepointIndependent base x y = differenceThrough (value y) (value x) (value base)

    betweenHasIntegral : ∀ x y → fst x ≤ℝ fst y →
      HasRiemannIntegralOn f (fst x) (fst y) (between x y)
    betweenHasIntegral x@(x₀ , a≤x , x≤b) y@(y₀ , a≤y , y≤b) x≤y =
      subst (HasRiemannIntegralOn f x₀ y₀)
        (sym (riemannIntegral-difference f a x₀ y₀ a≤x x≤y
          (value x , hasValue x) (integrable x₀ y₀ a≤x x≤y y≤b) (value y , hasValue y)))
        (snd (integrable x₀ y₀ a≤x x≤y y≤b))

    betweenAgreesWithIntegral : ∀ x y → fst x ≤ℝ fst y →
      ∀ result → HasRiemannIntegralOn f (fst x) (fst y) result → between x y ≡ result
    betweenAgreesWithIntegral x y x≤y result hasResult =
      riemannIntegralUnique (fst x) (fst y) x≤y f (between x y) result
        (betweenHasIntegral x y x≤y) hasResult

    betweenOfAntiderivative : ∀ F → IsRadiuswiseUniformDerivativeOn F f a b →
      ∀ x y → between x y ≡ F (fst y) - F (fst x)
    betweenOfAntiderivative F derivative x y =
      cong₂ _-_ (A.valueOfUniformAntiderivative F derivative y)
        (A.valueOfUniformAntiderivative F derivative x)
      ∙ differenceThrough (F (fst y)) (F (fst x)) (F a)

    betweenAbsBound : ∀ bound →
      (∀ z → a ≤ℝ z → z ≤ℝ b → absℝ (f z) ≤ℝ bound) →
      ∀ x y → absℝ (between x y) ≤ℝ absℝ (fst y - fst x) · bound
    betweenAbsBound bound bounded x@(x₀ , a≤x , x≤b) y@(y₀ , a≤y , y≤b) =
      orderCasesForBound x₀ y₀ (absℝ (between x y)) (absℝ (y₀ - x₀) · bound)
        (λ x≤y → subst (absℝ (between x y) ≤ℝ_)
          (cong (_· bound) (sym (absOfNonnegative (y₀ - x₀) (nonnegativeSub x₀ y₀ x≤y))))
          (riemannIntegral-absBoundOn x₀ y₀ x≤y f (between x y) bound (betweenHasIntegral x y x≤y)
            (λ z x≤z z≤y → bounded z (≤ℝ-trans a x₀ z a≤x x≤z) (≤ℝ-trans z y₀ b z≤y y≤b))))
        (λ y≤x → subst2 _≤ℝ_ (absSubComm (value x) (value y))
          (cong (_· bound) (sym (absOfNonnegative (x₀ - y₀) (nonnegativeSub y₀ x₀ y≤x))
            ∙ absSubComm x₀ y₀))
          (riemannIntegral-absBoundOn y₀ x₀ y≤x f (between y x) bound (betweenHasIntegral y x y≤x)
            (λ z y≤z z≤x → bounded z (≤ℝ-trans a y₀ z a≤y y≤z) (≤ℝ-trans z x₀ b z≤x x≤b))))

    valueMonotone : (∀ z → a ≤ℝ z → z ≤ℝ b → 0ℝ ≤ℝ f z) →
      ∀ x y → fst x ≤ℝ fst y → value x ≤ℝ value y
    valueMonotone nonnegative x@(x₀ , a≤x , x≤b) y@(y₀ , a≤y , y≤b) x≤y =
      addReflects≤R (value x) (value y) (- value x)
        (subst (_≤ℝ between x y) (sym (subSelf (value x)))
          (riemannIntegral-nonnegativeOn x₀ y₀ x≤y f (between x y) (betweenHasIntegral x y x≤y)
            (λ z x≤z z≤y → nonnegative z (≤ℝ-trans a x₀ z a≤x x≤z) (≤ℝ-trans z y₀ b z≤y y≤b))))

    -- Bounded integrands have Lipschitz primitives even when the integrand
    -- itself is discontinuous. Only the subinterval integrals are used.
    valueIsLipschitzWith : ∀ (bound : ℚ₊) →
      (∀ z → a ≤ℝ z → z ≤ℝ b → absℝ (f z) ≤ℝ rat (fst bound)) →
      IsLipschitzWith (ClosedIntervalPremetricSpace a b .snd) value (ℝPremetricSpace .snd) bound
    valueIsLipschitzWith bound bounded = islipschitzwith λ x y ε close →
      absDifference<→closeness (value x) (value y) (bound ·₊ ε)
        (≤<ℝ-trans (absℝ (value x - value y)) (absℝ (fst x - fst y) · rat (fst bound))
          (rat (fst (bound ·₊ ε))) (betweenAbsBound (rat (fst bound)) bounded y x)
          (subst ((absℝ (fst x - fst y) · rat (fst bound)) <ℝ_)
            (mulComm (rat (fst ε)) (rat (fst bound)) ∙ mul-rat (fst bound) (fst ε))
            (mulPres<PosR (absℝ (fst x - fst y)) (rat (fst ε)) (rat (fst bound))
              (positiveSlack bound) (closeness→absDifference< (fst x) (fst y) ε close))))

    valueIsUniformlyContinuous : ∀ (bound : ℚ₊) →
      (∀ z → a ≤ℝ z → z ≤ℝ b → absℝ (f z) ≤ℝ rat (fst bound)) →
      isUniformlyContinuous (ClosedIntervalPremetricSpace a b .snd) value (ℝPremetricSpace .snd)
    valueIsUniformlyContinuous bound bounded =
      isLipschitz→isUniformlyContinuous (ClosedIntervalPremetricSpace a b .snd) value (ℝPremetricSpace .snd)
        ∣ bound , valueIsLipschitzWith bound bounded ∣₁

    betweenUpperDerivative :
      isContinuous (ClosedIntervalPremetricSpace a b .snd) (f ∘ fst) (ℝPremetricSpace .snd) →
      ∀ x → IsDerivativeAlong (ClosedIntervalPremetricSpace a b .snd) fst (between x) (f ∘ fst)
    betweenUpperDerivative continuous x =
      subst (IsDerivativeAlong (ClosedIntervalPremetricSpace a b .snd) fst (between x))
        (funExt λ y → subZero (f (fst y)))
        (subHasDerivativeAlong (ClosedIntervalPremetricSpace a b .snd) fst
          value (λ _ → value x) (f ∘ fst) (λ _ → 0ℝ)
          (A.hasDerivative continuous)
          (constantHasDerivativeAlong (ClosedIntervalPremetricSpace a b .snd) fst (value x)))

    betweenLowerDerivative :
      isContinuous (ClosedIntervalPremetricSpace a b .snd) (f ∘ fst) (ℝPremetricSpace .snd) →
      ∀ y → IsDerivativeAlong (ClosedIntervalPremetricSpace a b .snd) fst
        (λ x → between x y) (λ x → - f (fst x))
    betweenLowerDerivative continuous y =
      subst (IsDerivativeAlong (ClosedIntervalPremetricSpace a b .snd) fst (λ x → between x y))
        (funExt λ x → zeroSub (f (fst x)))
        (subHasDerivativeAlong (ClosedIntervalPremetricSpace a b .snd) fst
          (λ _ → value y) value (λ _ → 0ℝ) (f ∘ fst)
          (constantHasDerivativeAlong (ClosedIntervalPremetricSpace a b .snd) fst (value y))
          (A.hasDerivative continuous))


module UniformlyContinuousIntervalIntegral (f : ℝ → ℝ) (a b : ℝ) (a≤b : a ≤ℝ b)
    (continuous : isUniformlyContinuous (ClosedIntervalPremetricSpace a b .snd) (f ∘ fst) (ℝPremetricSpace .snd)) where
  private
    module J = IntervalIntegral f a b a≤b (uniformContinuityIsIntegrableOnSubintervals f a b continuous)
  open J public

  opaque
    valueIsLipschitz : isLipschitz (ClosedIntervalPremetricSpace a b .snd) value (ℝPremetricSpace .snd)
    valueIsLipschitz = PT.map (λ { (bound , bounded) → bound , valueIsLipschitzWith bound bounded })
      (uniformContinuityIsBoundedOn f a b a≤b continuous)

    valueUniformlyContinuous : isUniformlyContinuous (ClosedIntervalPremetricSpace a b .snd) value (ℝPremetricSpace .snd)
    valueUniformlyContinuous = isLipschitz→isUniformlyContinuous
      (ClosedIntervalPremetricSpace a b .snd) value (ℝPremetricSpace .snd) valueIsLipschitz

  upperDerivative : ∀ x →
    IsDerivativeAlong (ClosedIntervalPremetricSpace a b .snd) fst (between x) (f ∘ fst)
  upperDerivative = betweenUpperDerivative
    (isUniformlyContinuous→isContinuous (ClosedIntervalPremetricSpace a b .snd) (f ∘ fst) (ℝPremetricSpace .snd) continuous)

  lowerDerivative : ∀ y → IsDerivativeAlong (ClosedIntervalPremetricSpace a b .snd) fst
    (λ x → between x y) (λ x → - f (fst x))
  lowerDerivative = betweenLowerDerivative
    (isUniformlyContinuous→isContinuous (ClosedIntervalPremetricSpace a b .snd) (f ∘ fst) (ℝPremetricSpace .snd) continuous)
