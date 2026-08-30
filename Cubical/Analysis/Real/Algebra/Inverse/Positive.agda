module Cubical.Analysis.Real.Algebra.Inverse.Positive where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Rationals.Base
open import Cubical.Data.Rationals.Inverse using (_⁻¹₊)
open import Cubical.Data.Rationals.Order as ℚ

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using
  (1ℝ; mulComm)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Algebra.Inverse.Bounded
open import Cubical.Analysis.Real.Algebra.Inverse.Compatibility
open import Cubical.Analysis.Real.Algebra.Inverse.Laws


gapLowerBound : ∀ {x} →
  (w : PositiveGap 0ℝ x) →
  rat (fst (fst w)) ≤ℝ x
gapLowerBound {x} (η , η-bound) =
  subst (_≤ℝ x)
    (addIdL (rat (fst η)))
    η-bound


private
  positiveReciprocalAtGapValue : ∀ x →
    PositiveGap 0ℝ x → ℝ
  positiveReciprocalAtGapValue x (η , _) =
    boundedReciprocalℝ η x

  positiveReciprocalAtGapConstant : ∀ x →
    2-Constant (positiveReciprocalAtGapValue x)
  positiveReciprocalAtGapConstant x
    w@(η , _) v@(θ , _) =
    boundedReciprocalCompatible
      η θ x
      (gapLowerBound w) (gapLowerBound v)


opaque
  positiveReciprocal : ∀ x →
    0ℝ <ℝ x → ℝ
  positiveReciprocal x =
    PT.rec→Set isSetℝ
      (positiveReciprocalAtGapValue x)
      (positiveReciprocalAtGapConstant x)

  positiveReciprocalAtGap : ∀ x
    (w : PositiveGap 0ℝ x) →
    positiveReciprocal x ∣ w ∣₁ ≡
    boundedReciprocalℝ (fst w) x
  positiveReciprocalAtGap x (η , η-bound) = refl


rationalPositiveGap : ∀ q →
  (0<q : 0 ℚ.< q) →
  PositiveGap 0ℝ (rat q)
rationalPositiveGap q 0<q =
  (q , 0<q) ,
  subst (_≤ℝ rat q)
    (sym (addIdL (rat q)))
    (≤ℝ-refl (rat q))


positiveReciprocal-rat : ∀ q →
  (0<q : 0 ℚ.< q) →
  (p : 0ℝ <ℝ rat q) →
  positiveReciprocal (rat q) p ≡
  rat (fst ((q , 0<q) ⁻¹₊))
positiveReciprocal-rat q 0<q p =
    cong (positiveReciprocal (rat q))
      (isProp<ℝ 0ℝ (rat q)
        p ∣ rationalPositiveGap q 0<q ∣₁)
  ∙ positiveReciprocalAtGap
      (rat q) (rationalPositiveGap q 0<q)
  ∙ boundedReciprocal-rat (q , 0<q) q
  ∙ cong rat
      (boundedReciprocalℚAbove
        (q , 0<q) q 0<q (ℚ.isRefl≤ q))


positiveReciprocalLaw : ∀ x
  (p : 0ℝ <ℝ x) →
  x · positiveReciprocal x p ≡ 1ℝ
positiveReciprocalLaw x p =
  PT.rec
    (isSetℝ (x · positiveReciprocal x p) 1ℝ)
    (λ (w@(η , _) : PositiveGap 0ℝ x) →
      cong (x ·_)
        (cong (positiveReciprocal x)
          (isProp<ℝ 0ℝ x p ∣ w ∣₁)
        ∙ positiveReciprocalAtGap x w)
      ∙ boundedReciprocalLaw
          η x (gapLowerBound w))
    p


positiveReciprocalLaw' : ∀ x
  (p : 0ℝ <ℝ x) →
  positiveReciprocal x p · x ≡ 1ℝ
positiveReciprocalLaw' x p =
  mulComm (positiveReciprocal x p) x
  ∙ positiveReciprocalLaw x p
