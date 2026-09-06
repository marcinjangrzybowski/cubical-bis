module Cubical.Analysis.Real.Series.PowerSeries.Exponential.Order where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties

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
open import Cubical.Analysis.Real.Algebra.Inverse.Positive
open import Cubical.Analysis.Real.Algebra.Inverse.Order
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Real.Order.Strict.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Located
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Addition
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Bounds


private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)

  opaque
    inverseFromProduct : ∀ a b (positive : 0ℝ <ℝ a) →
      a · b ≡ 1ℝ → b ≡ positiveReciprocal a positive
    inverseFromProduct a b positive product =
      sym (mulIdL b)
      ∙ cong (_· b) (sym (positiveReciprocalLaw' a positive))
      ∙ sym (mulAssoc (positiveReciprocal a positive) a b)
      ∙ cong (positiveReciprocal a positive ·_) product
      ∙ mulIdR (positiveReciprocal a positive)

    shiftNonnegative : ∀ x → 0ℝ ≤ℝ absℝ x + x
    shiftNonnegative x =
      subst (_≤ℝ absℝ x + x) (addInvL x)
        (addPres≤R (- x) (absℝ x) x (negLeAbs x))

    cancelShift : ∀ radius x → (- radius) + (radius + x) ≡ x
    cancelShift radius x =
      addAssoc (- radius) radius x
      ∙ cong (_+ x) (addInvL radius)
      ∙ addIdL x

    mulPredecessor : ∀ a b → a · (b - 1ℝ) ≡ a · b - a
    mulPredecessor a b =
      ℝRing.·DistR- a b 1ℝ
      ∙ cong (λ value → (a · b) - value) (mulIdR a)

    removeOneFromBound : ∀ x y → 1ℝ + x ≤ℝ y → x ≤ℝ y - 1ℝ
    removeOneFromBound x y bound =
      addReflects≤L x (y - 1ℝ) 1ℝ
        (subst (1ℝ + x ≤ℝ_)
          (sym (addComm 1ℝ (y - 1ℝ) ∙ subAddCancel y 1ℝ)) bound)


opaque
  exponentialEntireValue-negativePositive : ∀ x → 0ℝ ≤ℝ x →
    0ℝ <ℝ exponentialEntireValue (- x)
  exponentialEntireValue-negativePositive x nonnegative =
    subst (0ℝ <ℝ_)
      (sym (inverseFromProduct
        (exponentialEntireValue x) (exponentialEntireValue (- x)) positive
        (exponentialEntireValue-mul-negative x)))
      (positiveReciprocalPositive (exponentialEntireValue x) positive)
    where
    positive : 0ℝ <ℝ exponentialEntireValue x
    positive = exponentialEntireValue-positiveOnNonnegative x nonnegative

  -- Translate by |x| rather than deciding the sign of a completed real.
  exponentialEntireValue-positive : ∀ x → 0ℝ <ℝ exponentialEntireValue x
  exponentialEntireValue-positive x =
    subst (0ℝ <ℝ_)
      (sym (exponentialEntireValue-add (- absℝ x) (absℝ x + x))
        ∙ cong exponentialEntireValue (cancelShift (absℝ x) x))
      (mulPositive
        (exponentialEntireValue (- absℝ x))
        (exponentialEntireValue (absℝ x + x))
        (exponentialEntireValue-negativePositive (absℝ x) (absNonnegative x))
        (exponentialEntireValue-positiveOnNonnegative
          (absℝ x + x) (shiftNonnegative x)))

  exponentialEntireValue-nonnegative : ∀ x → 0ℝ ≤ℝ exponentialEntireValue x
  exponentialEntireValue-nonnegative x =
    <ℝ-weaken 0ℝ (exponentialEntireValue x) (exponentialEntireValue-positive x)

  exponentialEntireValue-negativeReciprocal : ∀ x →
    exponentialEntireValue (- x) ≡
    positiveReciprocal (exponentialEntireValue x) (exponentialEntireValue-positive x)
  exponentialEntireValue-negativeReciprocal x =
    inverseFromProduct (exponentialEntireValue x) (exponentialEntireValue (- x))
      (exponentialEntireValue-positive x) (exponentialEntireValue-mul-negative x)

  exponentialEntireValue-differenceFactorization : ∀ x y →
    exponentialEntireValue y - exponentialEntireValue x ≡
    exponentialEntireValue x · (exponentialEntireValue (y - x) - 1ℝ)
  exponentialEntireValue-differenceFactorization x y =
    cong (_- exponentialEntireValue x)
      (sym (cong exponentialEntireValue
        (addComm x (y - x) ∙ subAddCancel y x))
        ∙ exponentialEntireValue-add x (y - x))
    ∙ sym (mulPredecessor (exponentialEntireValue x) (exponentialEntireValue (y - x)))

  exponentialEntireValue-lowerDifferenceBound : ∀ x y → x ≤ℝ y →
    exponentialEntireValue x · (y - x) ≤ℝ
    exponentialEntireValue y - exponentialEntireValue x
  exponentialEntireValue-lowerDifferenceBound x y ordered =
    subst ((exponentialEntireValue x · (y - x)) ≤ℝ_)
      (sym (exponentialEntireValue-differenceFactorization x y))
      (mulPres≤L (y - x) (exponentialEntireValue (y - x) - 1ℝ)
        (exponentialEntireValue x)
        (0≤→isNonnegative (exponentialEntireValue x)
          (exponentialEntireValue-nonnegative x))
        (removeOneFromBound (y - x) (exponentialEntireValue (y - x))
          (exponentialEntireValue-linearLowerBound (y - x)
            (nonnegativeSub x y ordered))))

  exponentialEntireValue-strictlyIncreasing : ∀ x y → x <ℝ y →
    exponentialEntireValue x <ℝ exponentialEntireValue y
  exponentialEntireValue-strictlyIncreasing x y ordered =
    positiveSub→< (exponentialEntireValue x) (exponentialEntireValue y)
      (<≤ℝ-trans 0ℝ (exponentialEntireValue x · (y - x))
        (exponentialEntireValue y - exponentialEntireValue x)
        (mulPositive (exponentialEntireValue x) (y - x)
          (exponentialEntireValue-positive x) (positiveSub x y ordered))
        (exponentialEntireValue-lowerDifferenceBound x y (<ℝ-weaken x y ordered)))

  exponentialEntireValue-preserves≤ : ∀ x y → x ≤ℝ y →
    exponentialEntireValue x ≤ℝ exponentialEntireValue y
  exponentialEntireValue-preserves≤ x y ordered =
    addReflects≤R (exponentialEntireValue x) (exponentialEntireValue y)
      (- exponentialEntireValue x)
      (subst (_≤ℝ exponentialEntireValue y - exponentialEntireValue x)
        (sym (subSelf (exponentialEntireValue x)))
        (≤ℝ-trans 0ℝ (exponentialEntireValue x · (y - x))
          (exponentialEntireValue y - exponentialEntireValue x)
          (subst (_≤ℝ exponentialEntireValue x · (y - x))
            (ℝRing.0LeftAnnihilates (y - x))
            (mulPres≤R-0≤ 0ℝ (exponentialEntireValue x) (y - x)
              (nonnegativeSub x y ordered) (exponentialEntireValue-nonnegative x)))
          (exponentialEntireValue-lowerDifferenceBound x y ordered)))

  exponentialEntireValue-reflects≤ : ∀ x y →
    exponentialEntireValue x ≤ℝ exponentialEntireValue y → x ≤ℝ y
  exponentialEntireValue-reflects≤ x y ordered =
    notGreater→≤ℝ x y λ y<x →
      ≤ℝ→≯ (exponentialEntireValue x) (exponentialEntireValue y) ordered
        (exponentialEntireValue-strictlyIncreasing y x y<x)

  exponentialEntireValue-injective : ∀ x y →
    exponentialEntireValue x ≡ exponentialEntireValue y → x ≡ y
  exponentialEntireValue-injective x y equal =
    ≤ℝ-antisym x y
      (notGreater→≤ℝ x y λ y<x →
        <ℝ→≢ (exponentialEntireValue y) (exponentialEntireValue x)
          (exponentialEntireValue-strictlyIncreasing y x y<x) (sym equal))
      (notGreater→≤ℝ y x λ x<y →
        <ℝ→≢ (exponentialEntireValue x) (exponentialEntireValue y)
          (exponentialEntireValue-strictlyIncreasing x y x<y) equal)
