module Cubical.Analysis.Real.Integration.FundamentalTheorem.Consequences where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AdditiveGroup.Properties
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Real.Order.Strict.Multiplication
open import Cubical.Analysis.Real.Calculus.MeanValue.Uniform
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Base
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Comparison
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Extensionality
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Laws.Constant
open import Cubical.Analysis.Real.Integration.FundamentalTheorem.Algebra
open import Cubical.Analysis.Real.Integration.FundamentalTheorem.First

private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)

  zeroDifference→Path : ∀ x y → x - y ≡ 0ℝ → x ≡ y
  zeroDifference→Path x y differenceZero =
    sym (subAddCancel x y) ∙ cong (_+ y) differenceZero ∙ addIdL y

opaque
  uniformDerivativeNonnegative→monotoneOn : ∀ F f a b →
    IsRadiuswiseUniformDerivativeOn F f a b →
    (∀ z → a ≤ℝ z → z ≤ℝ b → 0ℝ ≤ℝ f z) →
    ∀ x y → a ≤ℝ x → x ≤ℝ y → y ≤ℝ b → F x ≤ℝ F y
  uniformDerivativeNonnegative→monotoneOn F f a b derivative nonnegative x y a≤x x≤y y≤b =
    addReflects≤R (F x) (F y) (- F x)
      (subst (_≤ℝ F y - F x) (sym (subSelf (F x)))
        (riemannIntegral-nonnegativeOn x y x≤y f (F y - F x)
          (uniformDerivativeHasIntegralIncrements F f a b derivative x y a≤x x≤y y≤b)
          (λ z x≤z z≤y → nonnegative z
            (≤ℝ-trans a x z a≤x x≤z) (≤ℝ-trans z y b z≤y y≤b))))

  uniformDerivativeLowerBoundOn : ∀ F f a b lower →
    IsRadiuswiseUniformDerivativeOn F f a b →
    (∀ z → a ≤ℝ z → z ≤ℝ b → lower ≤ℝ f z) →
    ∀ x y → a ≤ℝ x → x ≤ℝ y → y ≤ℝ b → (y - x) · lower ≤ℝ F y - F x
  uniformDerivativeLowerBoundOn F f a b lower derivative bounded x y a≤x x≤y y≤b =
    riemannIntegral-lowerBoundOn x y x≤y f (F y - F x) lower
      (uniformDerivativeHasIntegralIncrements F f a b derivative x y a≤x x≤y y≤b)
      (λ z x≤z z≤y → bounded z (≤ℝ-trans a x z a≤x x≤z) (≤ℝ-trans z y b z≤y y≤b))

  uniformDerivativeUpperBoundOn : ∀ F f a b upper →
    IsRadiuswiseUniformDerivativeOn F f a b →
    (∀ z → a ≤ℝ z → z ≤ℝ b → f z ≤ℝ upper) →
    ∀ x y → a ≤ℝ x → x ≤ℝ y → y ≤ℝ b → F y - F x ≤ℝ (y - x) · upper
  uniformDerivativeUpperBoundOn F f a b upper derivative bounded x y a≤x x≤y y≤b =
    riemannIntegral-upperBoundOn x y x≤y f (F y - F x) upper
      (uniformDerivativeHasIntegralIncrements F f a b derivative x y a≤x x≤y y≤b)
      (λ z x≤z z≤y → bounded z (≤ℝ-trans a x z a≤x x≤z) (≤ℝ-trans z y b z≤y y≤b))

  uniformDerivativePositiveLowerBound→strictlyMonotoneOn : ∀ F f a b lower →
    0ℝ <ℝ lower → IsRadiuswiseUniformDerivativeOn F f a b →
    (∀ z → a ≤ℝ z → z ≤ℝ b → lower ≤ℝ f z) →
    ∀ x y → a ≤ℝ x → x <ℝ y → y ≤ℝ b → F x <ℝ F y
  uniformDerivativePositiveLowerBound→strictlyMonotoneOn
    F f a b lower positive derivative bounded x y a≤x x<y y≤b =
    positiveSub→< (F x) (F y)
      (<≤ℝ-trans 0ℝ ((y - x) · lower) (F y - F x)
        (mulPositive (y - x) lower (positiveSub x y x<y) positive)
        (uniformDerivativeLowerBoundOn F f a b lower derivative bounded x y a≤x
          (<ℝ-weaken x y x<y) y≤b))

  sameUniformDerivativeSameIncrements : ∀ F G f a b →
    IsRadiuswiseUniformDerivativeOn F f a b → IsRadiuswiseUniformDerivativeOn G f a b →
    ∀ x → a ≤ℝ x → x ≤ℝ b → F x - F a ≡ G x - G a
  sameUniformDerivativeSameIncrements F G f a b first second x a≤x x≤b =
    riemannIntegralUnique a x a≤x f (F x - F a) (G x - G a)
      (uniformDerivativeHasIntegralIncrements F f a b first a x (≤ℝ-refl a) a≤x x≤b)
      (uniformDerivativeHasIntegralIncrements G f a b second a x (≤ℝ-refl a) a≤x x≤b)

  uniformAntiderivativesDifferByConstant : ∀ F G f a b →
    IsRadiuswiseUniformDerivativeOn F f a b → IsRadiuswiseUniformDerivativeOn G f a b →
    ∀ x → a ≤ℝ x → x ≤ℝ b → F x - G x ≡ F a - G a
  uniformAntiderivativesDifferByConstant F G f a b first second x a≤x x≤b =
    zeroDifference→Path (F x - G x) (F a - G a)
      (differenceOfDifferences (F x) (G x) (F a) (G a)
        ∙ cong (_- (G x - G a))
          (sameUniformDerivativeSameIncrements F G f a b first second x a≤x x≤b)
        ∙ subSelf (G x - G a))

  uniformAntiderivativeUniqueWithInitialValue : ∀ F G f a b →
    IsRadiuswiseUniformDerivativeOn F f a b → IsRadiuswiseUniformDerivativeOn G f a b →
    F a ≡ G a → ∀ x → a ≤ℝ x → x ≤ℝ b → F x ≡ G x
  uniformAntiderivativeUniqueWithInitialValue F G f a b first second initial x a≤x x≤b =
    zeroDifference→Path (F x) (G x)
      (uniformAntiderivativesDifferByConstant F G f a b first second x a≤x x≤b
        ∙ cong (_- G a) initial ∙ subSelf (G a))

  zeroUniformDerivativeIsConstantOn : ∀ F f a b →
    IsRadiuswiseUniformDerivativeOn F f a b →
    (∀ z → a ≤ℝ z → z ≤ℝ b → f z ≡ 0ℝ) →
    ∀ x → a ≤ℝ x → x ≤ℝ b → F x ≡ F a
  zeroUniformDerivativeIsConstantOn F f a b derivative zero x a≤x x≤b =
    zeroDifference→Path (F x) (F a)
      (riemannIntegralUnique a x a≤x (λ _ → 0ℝ) (F x - F a) 0ℝ
        (hasRiemannIntegral-congOn f (λ _ → 0ℝ) a x (F x - F a)
          (λ z a≤z z≤x → zero z a≤z (≤ℝ-trans z x b z≤x x≤b))
          (uniformDerivativeHasIntegralIncrements F f a b derivative a x (≤ℝ-refl a) a≤x x≤b))
        (subst (HasRiemannIntegralOn (λ _ → 0ℝ) a x)
          (ℝRing.0RightAnnihilates (x - a)) (constantHasRiemannIntegral a x 0ℝ)))
