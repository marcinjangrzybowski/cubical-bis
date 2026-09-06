module Cubical.Analysis.Real.Functions.Logarithm.Construction where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Algebra.CommRing.Base using (CommRing→Ring)
import Cubical.Algebra.Ring.Properties as RingProperties
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (1₊)

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
open import Cubical.Analysis.Real.Algebra.Positive
open import Cubical.Analysis.Real.Algebra.Inverse.Positive
open import Cubical.Analysis.Real.Algebra.Inverse.Order
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Real.Order.Strict.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Located
open import Cubical.Analysis.Real.Domain.OpenRadius
open import Cubical.Analysis.Real.Series.PowerSeries.Logarithm.Value


private
  module Ring = RingProperties.RingTheory (CommRing→Ring ℝCommRing)

  onePositive : 0ℝ <ℝ 1ℝ
  onePositive = snd (positiveRat 1₊)


-- The change of variables t = (y - 1)/(y + 1) places every positive real
-- strictly inside the convergence domain of the local logarithm series.
logarithmTransformDenominatorPositive : ∀ (value : ℝ>0) →
  0ℝ <ℝ fst value + 1ℝ
logarithmTransformDenominatorPositive value =
  subst (λ lower → lower <ℝ fst value + 1ℝ) (addIdL 0ℝ)
    (<ℝ-add 0ℝ (fst value) 0ℝ 1ℝ (snd value) onePositive)


logarithmTransformReciprocal : ℝ>0 → ℝ
logarithmTransformReciprocal value =
  positiveReciprocal (fst value + 1ℝ)
    (logarithmTransformDenominatorPositive value)


logarithmTransform : ℝ>0 → ℝ
logarithmTransform value =
  (fst value - 1ℝ) · logarithmTransformReciprocal value


opaque
  logarithmTransformNumeratorLaw : ∀ value →
    logarithmTransform value · (fst value + 1ℝ) ≡ fst value - 1ℝ
  logarithmTransformNumeratorLaw value =
    sym (mulAssoc (fst value - 1ℝ) (logarithmTransformReciprocal value)
      (fst value + 1ℝ))
    ∙ cong ((fst value - 1ℝ) ·_)
        (positiveReciprocalLaw' (fst value + 1ℝ)
          (logarithmTransformDenominatorPositive value))
    ∙ mulIdR (fst value - 1ℝ)

  logarithmTransformSumLaw : ∀ value →
    logarithmTransform value · fst value + logarithmTransform value ≡ fst value - 1ℝ
  logarithmTransformSumLaw value =
    cong (logarithmTransform value · fst value +_)
      (sym (mulIdR (logarithmTransform value)))
    ∙ sym (mulDistR (logarithmTransform value) (fst value) 1ℝ)
    ∙ logarithmTransformNumeratorLaw value

  logarithmTransformLessThanOne : ∀ value → logarithmTransform value <ℝ 1ℝ
  logarithmTransformLessThanOne value =
    subst (logarithmTransform value <ℝ_)
      (positiveReciprocalLaw (fst value + 1ℝ)
        (logarithmTransformDenominatorPositive value))
      (mulPres<PosR (fst value - 1ℝ) (fst value + 1ℝ)
        (logarithmTransformReciprocal value)
        (positiveReciprocalPositive (fst value + 1ℝ)
          (logarithmTransformDenominatorPositive value))
        (<ℝ-addL (- 1ℝ) 1ℝ (fst value)
          (<ℝ-trans (- 1ℝ) 0ℝ 1ℝ
            (subst ((- 1ℝ) <ℝ_) negZero (<ℝ-neg 0ℝ 1ℝ onePositive))
            onePositive)))

  logarithmTransformNegativeLessThanOne : ∀ value →
    (- logarithmTransform value) <ℝ 1ℝ
  logarithmTransformNegativeLessThanOne value =
    subst2 _<ℝ_
      (cong (_· reciprocal) (sym (negSub y 1ℝ))
        ∙ Ring.-DistL· (y - 1ℝ) reciprocal)
      (positiveReciprocalLaw (y + 1ℝ)
        (logarithmTransformDenominatorPositive value))
      (mulPres<PosR (1ℝ - y) (y + 1ℝ) reciprocal
        (positiveReciprocalPositive (y + 1ℝ)
          (logarithmTransformDenominatorPositive value))
        (subst ((1ℝ - y) <ℝ_) (addComm 1ℝ y)
          (<ℝ-addL (- y) y 1ℝ
            (<ℝ-trans (- y) 0ℝ y
              (subst ((- y) <ℝ_) negZero (<ℝ-neg 0ℝ y (snd value)))
              (snd value)))))
    where
    y : ℝ
    y = fst value

    reciprocal : ℝ
    reciprocal = logarithmTransformReciprocal value

  logarithmTransformInside : ∀ value → absℝ (logarithmTransform value) <ℝ 1ℝ
  logarithmTransformInside value =
    subst (_<ℝ 1ℝ) (sym (absAsMax (logarithmTransform value)))
      (maxStrictUpper (logarithmTransform value) (- logarithmTransform value) 1ℝ
        (logarithmTransformLessThanOne value)
        (logarithmTransformNegativeLessThanOne value))

  logarithmTransformNegativeInside : ∀ value →
    absℝ (- logarithmTransform value) <ℝ 1ℝ
  logarithmTransformNegativeInside value =
    subst (_<ℝ 1ℝ) (sym (absNeg (logarithmTransform value)))
      (logarithmTransformInside value)


logarithmTransformPoint : ℝ>0 → OpenAbsRadius 1ℝ
logarithmTransformPoint value = logarithmTransform value , logarithmTransformInside value


-- This is a total, choice-free candidate.  Its identification as the inverse
-- of exponential is a separate compatibility theorem, not an assumption in
-- this construction.
logarithmSeries : ℝ>0 → ℝ
logarithmSeries value =
  negativeLogOneMinus (logarithmTransform value) (logarithmTransformInside value)
  - negativeLogOneMinus (- logarithmTransform value)
      (logarithmTransformNegativeInside value)


private
  opaque
    transformAtOne : ∀ value → fst value ≡ 1ℝ → logarithmTransform value ≡ 0ℝ
    transformAtOne value at-one =
      cong (_· logarithmTransformReciprocal value)
        (cong (_- 1ℝ) at-one ∙ subSelf 1ℝ)
      ∙ Ring.0LeftAnnihilates (logarithmTransformReciprocal value)

    cancelSummand : ∀ a b → ((a + b) + 1ℝ) - a ≡ 1ℝ + b
    cancelSummand a b =
      cong (_+ (- a)) (sym (addAssoc a b 1ℝ))
      ∙ sym (addAssoc a (b + 1ℝ) (- a))
      ∙ cong (a +_) (addComm (b + 1ℝ) (- a))
      ∙ addAssoc a (- a) (b + 1ℝ)
      ∙ cong (_+ (b + 1ℝ)) (addInvR a)
      ∙ addIdL (b + 1ℝ)
      ∙ addComm b 1ℝ

    localZero : ∀ x (inside : absℝ x <ℝ 1ℝ) → x ≡ 0ℝ →
      negativeLogOneMinus x inside ≡ 0ℝ
    localZero x inside x=0 =
      cong (λ point → negativeLogOneMinus (fst point) (snd point))
        (Σ≡Prop (λ z → isProp<ℝ (absℝ z) 1ℝ)
          {u = x , inside} {v = 0ℝ , subst (λ z → absℝ z <ℝ 1ℝ) x=0 inside} x=0)
      ∙ negativeLogOneMinus-zero _

    seriesAtTransformZero : ∀ value → logarithmTransform value ≡ 0ℝ →
      logarithmSeries value ≡ 0ℝ
    seriesAtTransformZero value transform-zero =
      cong₂ _-_
        (localZero (logarithmTransform value) (logarithmTransformInside value)
          transform-zero)
        (localZero (- logarithmTransform value) (logarithmTransformNegativeInside value)
          (cong -_ transform-zero ∙ negZero))
      ∙ subSelf 0ℝ


opaque
  logarithmTransformRatioLaw : ∀ value →
    (1ℝ - logarithmTransform value) · fst value ≡ 1ℝ + logarithmTransform value
  logarithmTransformRatioLaw value =
    Ring.·DistL- 1ℝ (logarithmTransform value) (fst value)
    ∙ cong (_- (logarithmTransform value · fst value)) (mulIdL (fst value))
    ∙ cong (_- (logarithmTransform value · fst value))
        (sym (subAddCancel (fst value) 1ℝ)
          ∙ cong (_+ 1ℝ) (sym (logarithmTransformSumLaw value)))
    ∙ cancelSummand (logarithmTransform value · fst value) (logarithmTransform value)

  logarithmTransform-atOne : ∀ value → fst value ≡ 1ℝ → logarithmTransform value ≡ 0ℝ
  logarithmTransform-atOne = transformAtOne

  logarithmSeries-atOne : ∀ value → fst value ≡ 1ℝ → logarithmSeries value ≡ 0ℝ
  logarithmSeries-atOne value at-one =
    seriesAtTransformZero value (transformAtOne value at-one)
