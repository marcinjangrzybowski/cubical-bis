module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Damped.Bounds where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Int.Fast using (pos)
open import Cubical.Data.Nat.Literals
open import Cubical.Data.NatPlusOne using (1+_)
open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Base as ℚ using (ℚ; [_/_]; eq/; fromNatℚ)
import Cubical.Data.Rationals.Order as ℚ
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Unit using (tt)
open import Cubical.Algebra.CommRing
import Cubical.Algebra.Ring.Properties as RingProperties
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AdditiveGroup.Properties
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Real.Order.Strict.Multiplication
open import Cubical.Analysis.Real.Calculus.MeanValue.Uniform
open import Cubical.Analysis.Real.Integration.FundamentalTheorem.Consequences
open import Cubical.Analysis.Real.Integration.Partition.Overlap using (orderCasesForBound)
open import Cubical.Analysis.Real.Series.Geometric.Rational using (halfℚ; halfℚPath)
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.SharpBounds
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Estimates.UniformDerivative
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Bishop.BaseInterval

private
  module R = RingProperties.RingTheory (CommRing→Ring ℝCommRing)

damping : ℝ
damping = rat [ pos 1 / 1+ 1 ]

sineLower : ℝ
sineLower = rat [ pos 1 / 1+ 3 ]

contraction : ℝ
contraction = rat [ pos 7 / 1+ 7 ]

step : ℝ → ℝ
step x = x + damping · cosℝ x

-- A quantitative prefix invariant is stable under constructive order
-- cases. Strict positivity follows from its positive endpoint value.
CosinePrefix : ℝ → Type₀
CosinePrefix x = (0ℝ ≤ℝ x) × (0ℝ <ℝ cosℝ x) ×
  (∀ z → 0ℝ ≤ℝ z → z ≤ℝ x → cosℝ x ≤ℝ cosℝ z)

opaque
  damping-positive : 0ℝ <ℝ damping
  damping-positive = <ℚ→<ℝ 0 [ pos 1 / 1+ 1 ] (ℚ.pos<pos tt)

  damping-nonnegative : 0ℝ ≤ℝ damping
  damping-nonnegative = <ℝ-weaken 0ℝ damping damping-positive

  damping≤one : damping ≤ℝ 1ℝ
  damping≤one = invEq (rat≤rat≃ [ pos 1 / 1+ 1 ] 1) (ℚ.<Weaken≤ _ _ (ℚ.pos<pos tt))

  contraction-nonnegative : 0ℝ ≤ℝ contraction
  contraction-nonnegative = <ℝ-weaken 0ℝ contraction
    (<ℚ→<ℝ 0 [ pos 7 / 1+ 7 ] (ℚ.pos<pos tt))

  contraction<one : contraction <ℝ 1ℝ
  contraction<one = <ℚ→<ℝ [ pos 7 / 1+ 7 ] 1 (ℚ.pos<pos tt)

  damping≤contraction : damping ≤ℝ contraction
  damping≤contraction = invEq (rat≤rat≃ [ pos 1 / 1+ 1 ] [ pos 7 / 1+ 7 ])
    (ℚ.<Weaken≤ _ _ (ℚ.pos<pos tt))

  damping-sum : damping + damping ≡ 1ℝ
  damping-sum = rat+rat [ pos 1 / 1+ 1 ] [ pos 1 / 1+ 1 ] ∙ cong rat (eq/ _ _ refl)

  damping-square : damping · damping ≡ sineLower
  damping-square = mul-rat [ pos 1 / 1+ 1 ] [ pos 1 / 1+ 1 ] ∙ cong rat (eq/ _ _ refl)

  contraction-path : 1ℝ - damping · sineLower ≡ contraction
  contraction-path = cong (λ z → 1ℝ - z) (mul-rat [ pos 1 / 1+ 1 ] [ pos 1 / 1+ 3 ])
    ∙ sub-rat 1 ([ pos 1 / 1+ 1 ] ℚ.· [ pos 1 / 1+ 3 ]) ∙ cong rat (eq/ _ _ refl)

  halfRemaining : ∀ v → v - damping · v ≡ damping · v
  halfRemaining v =
    cong (λ z → z - damping · v)
      (sym (mulIdL v) ∙ cong (_· v) (sym damping-sum) ∙ mulDistL damping damping v)
    ∙ R.plusMinus (damping · v) (damping · v)

  half≤self : ∀ v → 0ℝ ≤ℝ v → damping · v ≤ℝ v
  half≤self v p = subst (damping · v ≤ℝ_) (mulIdL v)
    (mulPres≤R-0≤ damping 1ℝ v p damping≤one)

  difference≤zero : ∀ a b → a - b ≤ℝ 0ℝ → a ≤ℝ b
  difference≤zero a b p = addReflects≤R a b (- b)
    (subst (a - b ≤ℝ_) (sym (subSelf b)) p)

  subBound→lower : ∀ a b r → a - b ≤ℝ r → a - r ≤ℝ b
  subBound→lower a b r p = addReflects≤R (a - r) b r
    (subst2 _≤ℝ_ (sym (subAddCancel a r)) (addComm r b)
      (subst (_≤ℝ r + b) (subAddCancel a b)
        (addPres≤R (a - b) r b p)))

  cosℝ-ordered-lower : ∀ x y → x ≤ℝ y → cosℝ x - (y - x) ≤ℝ cosℝ y
  cosℝ-ordered-lower x y p = subBound→lower (cosℝ x) (cosℝ y) (y - x)
    (≤ℝ-trans (cosℝ x - cosℝ y) (absℝ (cosℝ x - cosℝ y)) (y - x)
      (leAbs (cosℝ x - cosℝ y))
      (subst2 _≤ℝ_ (absSubComm (cosℝ y) (cosℝ x)) (mulIdL (y - x))
        (radiuswiseUniformDerivativeBound cosℝ (λ z → - sinℝ z)
          cosℝHasUniformDerivative x y p 1ℝ
          (λ z → subst (_≤ℝ 1ℝ) (sym (absNeg (sinℝ z))) (sinℝ-abs≤one z)))))

  sineMonotoneOn : ∀ b →
    (∀ z → 0ℝ ≤ℝ z → z ≤ℝ b → 0ℝ ≤ℝ cosℝ z) →
    ∀ x y → 0ℝ ≤ℝ x → x ≤ℝ y → y ≤ℝ b → sinℝ x ≤ℝ sinℝ y
  sineMonotoneOn b positive = uniformDerivativeNonnegative→monotoneOn sinℝ cosℝ 0ℝ b
    (radiuswiseUniformDerivative→onInterval sinℝ cosℝ 0ℝ b sinℝHasUniformDerivative) positive

  sineNonnegativeOn : ∀ b →
    (∀ z → 0ℝ ≤ℝ z → z ≤ℝ b → 0ℝ ≤ℝ cosℝ z) →
    ∀ z → 0ℝ ≤ℝ z → z ≤ℝ b → 0ℝ ≤ℝ sinℝ z
  sineNonnegativeOn b positive z left right =
    subst (_≤ℝ sinℝ z) sinℝ-zero
      (sineMonotoneOn b positive 0ℝ z (≤ℝ-refl 0ℝ) left right)

  cosineAntitoneOn : ∀ b →
    (∀ z → 0ℝ ≤ℝ z → z ≤ℝ b → 0ℝ ≤ℝ sinℝ z) →
    ∀ x y → 0ℝ ≤ℝ x → x ≤ℝ y → y ≤ℝ b → cosℝ y ≤ℝ cosℝ x
  cosineAntitoneOn b positive x y left ordered right =
    difference≤zero (cosℝ y) (cosℝ x)
      (subst (cosℝ y - cosℝ x ≤ℝ_) (R.0RightAnnihilates (y - x))
        (uniformDerivativeUpperBoundOn cosℝ (λ z → - sinℝ z) 0ℝ b 0ℝ
          (radiuswiseUniformDerivative→onInterval cosℝ (λ z → - sinℝ z) 0ℝ b cosℝHasUniformDerivative)
          (λ z l r → subst ((- sinℝ z) ≤ℝ_) negZero (negPres≤ 0ℝ (sinℝ z) (positive z l r)))
          x y left ordered right))

  step-increasing : ∀ x → 0ℝ <ℝ cosℝ x → x ≤ℝ step x
  step-increasing x positive = subst (_≤ℝ step x) (addIdR x)
    (addPres≤L 0ℝ (damping · cosℝ x) x
      (<ℝ-weaken 0ℝ (damping · cosℝ x)
        (mulPositive damping (cosℝ x) damping-positive positive)))

  prefixCosineNonnegative : ∀ x → CosinePrefix x →
    ∀ z → 0ℝ ≤ℝ z → z ≤ℝ x → 0ℝ ≤ℝ cosℝ z
  prefixCosineNonnegative x (nonnegative , positive , minimum) z l r =
    ≤ℝ-trans 0ℝ (cosℝ x) (cosℝ z) (<ℝ-weaken 0ℝ (cosℝ x) positive) (minimum z l r)

  step-prefix : ∀ x → CosinePrefix x → CosinePrefix (step x)
  step-prefix x invariant@(nonnegative , positive , minimum) =
    next-nonnegative , next-positive ,
      (λ z l r → cosineAntitoneOn (step x)
        (sineNonnegativeOn (step x) next-prefix-nonnegative)
        z (step x) l r (≤ℝ-refl (step x)))
    where
    t : ℝ
    t = damping · cosℝ x

    next-nonnegative : 0ℝ ≤ℝ step x
    next-nonnegative = ≤ℝ-trans 0ℝ x (step x) nonnegative (step-increasing x positive)

    coarse : ∀ z → 0ℝ ≤ℝ z → z ≤ℝ step x → t ≤ℝ cosℝ z
    coarse z l r = orderCasesForBound x z t (cosℝ z)
      (λ x≤z → ≤ℝ-trans t (cosℝ x - (z - x)) (cosℝ z)
        (subst (_≤ℝ cosℝ x - (z - x)) (halfRemaining (cosℝ x))
          (addPres≤L (- t) (- (z - x)) (cosℝ x)
            (negPres≤ (z - x) t
              (subst (z - x ≤ℝ_) (cong (_+ (- x)) (addComm x t) ∙ R.plusMinus t x)
                (addPres≤R z (step x) (- x) r)))))
        (cosℝ-ordered-lower x z x≤z))
      (λ z≤x → ≤ℝ-trans t (cosℝ x) (cosℝ z)
        (half≤self (cosℝ x) (<ℝ-weaken 0ℝ (cosℝ x) positive)) (minimum z l z≤x))

    next-prefix-positive : ∀ z → 0ℝ ≤ℝ z → z ≤ℝ step x → 0ℝ <ℝ cosℝ z
    next-prefix-positive z l r = <≤ℝ-trans 0ℝ t (cosℝ z)
      (mulPositive damping (cosℝ x) damping-positive positive) (coarse z l r)

    next-prefix-nonnegative : ∀ z → 0ℝ ≤ℝ z → z ≤ℝ step x → 0ℝ ≤ℝ cosℝ z
    next-prefix-nonnegative z l r = <ℝ-weaken 0ℝ (cosℝ z) (next-prefix-positive z l r)

    next-positive : 0ℝ <ℝ cosℝ (step x)
    next-positive = next-prefix-positive (step x) next-nonnegative (≤ℝ-refl (step x))

  initial-prefix : CosinePrefix 0ℝ
  initial-prefix = ≤ℝ-refl 0ℝ ,
    subst (0ℝ <ℝ_) (sym cosℝ-zero) (<ℚ→<ℝ 0 1 (ℚ.pos<pos tt)) ,
    λ z l r → subst (cosℝ 0ℝ ≤ℝ_) (cong cosℝ (≤ℝ-antisym 0ℝ z l r)) (≤ℝ-refl (cosℝ 0ℝ))

  sineLowerAtDamping : sineLower ≤ℝ sinℝ damping
  sineLowerAtDamping = subst2 _≤ℝ_
    (cong (_· damping) (subZero damping) ∙ damping-square)
    (cong (λ z → sinℝ damping - z) sinℝ-zero ∙ subZero (sinℝ damping))
    (uniformDerivativeLowerBoundOn sinℝ cosℝ 0ℝ damping damping
      (radiuswiseUniformDerivative→onInterval sinℝ cosℝ 0ℝ damping sinℝHasUniformDerivative)
      (λ z l r → subst (_≤ℝ cosℝ z) (cong rat halfℚPath)
        (half≤cosℝ-onUnitInterval z l (≤ℝ-trans z damping 1ℝ r damping≤one)))
      0ℝ damping (≤ℝ-refl 0ℝ) damping-nonnegative (≤ℝ-refl damping))

  contractAlgebra : ∀ v → (damping · v) · (- sineLower) + v ≡ contraction · v
  contractAlgebra v = addComm ((damping · v) · (- sineLower)) v
    ∙ cong (v +_) (R.-DistR· (damping · v) sineLower
      ∙ cong -_ (sym (mulAssoc damping v sineLower)
        ∙ cong (damping ·_) (mulComm v sineLower) ∙ mulAssoc damping sineLower v))
    ∙ cong (λ z → z - (damping · sineLower) · v) (sym (mulIdL v))
    ∙ sym (R.·DistL- 1ℝ (damping · sineLower) v)
    ∙ cong (_· v) contraction-path

  step-contracts : ∀ x → CosinePrefix x → damping ≤ℝ x →
    cosℝ (step x) ≤ℝ contraction · cosℝ x
  step-contracts x invariant@(nonnegative , positive , minimum) damping≤x =
    subst2 _≤ℝ_ (subAddCancel (cosℝ (step x)) (cosℝ x))
      (cong (_+ cosℝ x)
        (cong (_· (- sineLower))
          (cong (_+ (- x)) (addComm x (damping · cosℝ x))
            ∙ R.plusMinus (damping · cosℝ x) x))
        ∙ contractAlgebra (cosℝ x))
      (addPres≤R (cosℝ (step x) - cosℝ x) ((step x - x) · (- sineLower)) (cosℝ x)
        (uniformDerivativeUpperBoundOn cosℝ (λ z → - sinℝ z) x (step x) (- sineLower)
          (radiuswiseUniformDerivative→onInterval cosℝ (λ z → - sinℝ z) x (step x) cosℝHasUniformDerivative)
          (λ z l r → negPres≤ sineLower (sinℝ z)
            (≤ℝ-trans sineLower (sinℝ damping) (sinℝ z) sineLowerAtDamping
              (sineMonotoneOn (step x)
                (prefixCosineNonnegative (step x) (step-prefix x invariant))
                damping z damping-nonnegative (≤ℝ-trans damping x z damping≤x l) r)))
          x (step x) (≤ℝ-refl x) (step-increasing x positive) (≤ℝ-refl (step x))))
