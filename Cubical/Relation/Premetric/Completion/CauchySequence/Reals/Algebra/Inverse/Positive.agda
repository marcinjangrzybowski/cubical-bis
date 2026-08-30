module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Inverse.Positive where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Base
open import Cubical.Data.Rationals.Inverse using (_⁻¹₊)
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
  using (mul-comm)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Inverse.Bounded
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Inverse.Compatibility
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Inverse.Laws


gapLowerBound : ∀ {x} →
  (w : PositiveGap (Real.ιℚ 0) x) →
  Real.ιℚ (fst (width w)) ≤ℝ x
gapLowerBound {x} w =
  subst (_≤ℝ x)
    (add-zero-left (Real.ιℚ (fst (width w))))
    (bound w)


private
  positiveReciprocalAtGapValue : ∀ x →
    PositiveGap (Real.ιℚ 0) x → Real.ℝ
  positiveReciprocalAtGapValue x w =
    boundedReciprocalℝ (width w) x

  positiveReciprocalAtGapConstant : ∀ x →
    2-Constant (positiveReciprocalAtGapValue x)
  positiveReciprocalAtGapConstant x w v =
    boundedReciprocalCompatible
      (width w) (width v) x
      (gapLowerBound w) (gapLowerBound v)


opaque
  positiveReciprocal : ∀ x →
    Real.ιℚ 0 <ℝ x → Real.ℝ
  positiveReciprocal x =
    PT.rec→Set Real.Base.isSetCompletion
      (positiveReciprocalAtGapValue x)
      (positiveReciprocalAtGapConstant x)

  positiveReciprocalAtGap : ∀ x
    (w : PositiveGap (Real.ιℚ 0) x) →
    positiveReciprocal x ∣ w ∣₁ ≡
    boundedReciprocalℝ (width w) x
  positiveReciprocalAtGap x w = refl


rationalPositiveGap : ∀ q →
  (0<q : 0 ℚ.< q) →
  PositiveGap (Real.ιℚ 0) (Real.ιℚ q)
rationalPositiveGap q 0<q =
  positiveGap (q , 0<q)
    (subst (_≤ℝ Real.ιℚ q)
      (sym (add-zero-left (Real.ιℚ q)))
      (≤ℝ-refl (Real.ιℚ q)))


positiveReciprocal-ι : ∀ q →
  (0<q : 0 ℚ.< q) →
  (p : Real.ιℚ 0 <ℝ Real.ιℚ q) →
  positiveReciprocal (Real.ιℚ q) p ≡
  Real.ιℚ (fst ((q , 0<q) ⁻¹₊))
positiveReciprocal-ι q 0<q p =
    cong (positiveReciprocal (Real.ιℚ q))
      (isProp<ℝ (Real.ιℚ 0) (Real.ιℚ q)
        p ∣ rationalPositiveGap q 0<q ∣₁)
  ∙ positiveReciprocalAtGap
      (Real.ιℚ q) (rationalPositiveGap q 0<q)
  ∙ boundedReciprocal-ι (q , 0<q) q
  ∙ cong Real.ιℚ
      (boundedReciprocalℚAbove
        (q , 0<q) q 0<q (ℚ.isRefl≤ q))


positiveReciprocalLaw : ∀ x
  (p : Real.ιℚ 0 <ℝ x) →
  x Mul.· positiveReciprocal x p ≡ Real.ιℚ 1
positiveReciprocalLaw x p =
  PT.rec
    (Real.Base.isSetCompletion
      (x Mul.· positiveReciprocal x p) (Real.ιℚ 1))
    (λ w →
      cong (x Mul.·_)
        (cong (positiveReciprocal x)
          (isProp<ℝ (Real.ιℚ 0) x p ∣ w ∣₁)
        ∙ positiveReciprocalAtGap x w)
      ∙ boundedReciprocalLaw
          (width w) x (gapLowerBound w))
    p


positiveReciprocalLaw' : ∀ x
  (p : Real.ιℚ 0 <ℝ x) →
  positiveReciprocal x p Mul.· x ≡ Real.ιℚ 1
positiveReciprocalLaw' x p =
  mul-comm (positiveReciprocal x p) x
  ∙ positiveReciprocalLaw x p
