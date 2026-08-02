module Cubical.HITs.CauchyRealsP.Algebra.Inverse.Positive where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Inverse using (_⁻¹₊)
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra.AdditionLaws
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Base
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Strict
open import Cubical.HITs.CauchyRealsP.Algebra.Multiplication
open import Cubical.HITs.CauchyRealsP.Algebra.Inverse.Bounded
open import Cubical.HITs.CauchyRealsP.Algebra.Inverse.Compatibility
open import Cubical.HITs.CauchyRealsP.Algebra.Inverse.Laws

gapLowerBound : ∀ {x} →
  (w : PositiveGap 0 x) →
  rat (fst (width w)) ≤ℝ x
gapLowerBound {x} w =
  subst (_≤ℝ x)
    (addIdL (rat (fst (width w))))
    (gapBoundElim
      0 x (width w) (bound w))

private
  positiveReciprocalAtGapValue :
    ∀ x → PositiveGap 0 x → ℝ
  positiveReciprocalAtGapValue x w =
    boundedReciprocalℝ (width w) x

  positiveReciprocalAtGapConstant :
    ∀ x → 2-Constant (positiveReciprocalAtGapValue x)
  positiveReciprocalAtGapConstant x w v =
    boundedReciprocalCompatible
      (width w) (width v) x
      (gapLowerBound w)
      (gapLowerBound v)

opaque
  positiveReciprocal : ∀ x →
    0 <ℝ x →
    ℝ
  positiveReciprocal x =
    PT.rec→Set isSetℝ
      (positiveReciprocalAtGapValue x)
      (positiveReciprocalAtGapConstant x)

  positiveReciprocalAtGap :
    ∀ x (w : PositiveGap 0 x) →
    positiveReciprocal x ∣ w ∣₁ ≡
    boundedReciprocalℝ (width w) x
  positiveReciprocalAtGap x w =
    refl

rationalPositiveGap : ∀ q →
  (0<q : 0 ℚ.< q) →
  PositiveGap 0 (rat q)
rationalPositiveGap q 0<q =
  positiveGap
    (q , 0<q)
    (gapBoundIntro
      0 (rat q) (q , 0<q)
      (subst (_≤ℝ rat q)
        (sym (addIdL (rat q)))
        (≤ℝ-refl (rat q))))

positiveReciprocal-rat : ∀ q →
  (0<q : 0 ℚ.< q) →
  (p : 0 <ℝ rat q) →
  positiveReciprocal (rat q) p ≡
  rat (fst ((q , 0<q) ⁻¹₊))
positiveReciprocal-rat q 0<q p =
  cong (positiveReciprocal (rat q))
    (isProp<ℝ 0 (rat q)
      p ∣ rationalPositiveGap q 0<q ∣₁)
  ∙ positiveReciprocalAtGap
      (rat q) (rationalPositiveGap q 0<q)
  ∙ boundedReciprocal-rat (q , 0<q) q
  ∙ cong rat
      (boundedReciprocalℚAbove
        (q , 0<q) q 0<q
        (ℚ.isRefl≤ q))

positiveReciprocalLaw : ∀ x (p : 0 <ℝ x) →
  x · positiveReciprocal x p ≡ 1
positiveReciprocalLaw x p =
  PT.rec
    (isSetℝ (x · positiveReciprocal x p) 1)
    (λ w →
      cong (x ·_)
        (cong (positiveReciprocal x)
          (isProp<ℝ 0 x p ∣ w ∣₁)
        ∙ positiveReciprocalAtGap x w)
      ∙ boundedReciprocalLaw
          (width w) x (gapLowerBound w))
    p

positiveReciprocalLaw' : ∀ x (p : 0 <ℝ x) →
  positiveReciprocal x p · x ≡ 1
positiveReciprocalLaw' x p =
  mulComm (positiveReciprocal x p) x
  ∙ positiveReciprocalLaw x p
