module Cubical.HITs.CauchyRealsP.Algebra.Inverse.Signed where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring

import Cubical.Data.Rationals.Inverse as ℚInv
open import Cubical.Data.Sum as ⊎

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra.Negation
open import Cubical.HITs.CauchyRealsP.Algebra.AdditiveGroupLaws
open import Cubical.HITs.CauchyRealsP.Algebra.CommRing
open import Cubical.HITs.CauchyRealsP.Algebra.Multiplication
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Apartness
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Strict
open import Cubical.HITs.CauchyRealsP.Algebra.Order.MultiplicativeApartness
open import Cubical.HITs.CauchyRealsP.Algebra.Inverse.Positive
open import Cubical.HITs.CauchyRealsP.Algebra.Inverse.Order

private
  module ℝRing =
    RingTheory (CommRing→Ring ℝCommRing)

inverseℝ : ∀ x →
  0 ＃ x →
  ℝ
inverseℝ x (inl 0<x) =
  positiveReciprocal x 0<x
inverseℝ x (inr x<0) =
  - positiveReciprocal (- x)
      (negativeNegationPositive x<0)

inverseℝProofIrrelevant : ∀ x (p q : 0 ＃ x) →
  inverseℝ x p ≡ inverseℝ x q
inverseℝProofIrrelevant x p q =
  cong (inverseℝ x) (isProp＃ 0 x p q)

inverseℝLaw : ∀ x (p : 0 ＃ x) →
  x · inverseℝ x p ≡ 1
inverseℝLaw x (inl 0<x) =
  positiveReciprocalLaw x 0<x
inverseℝLaw x (inr x<0) =
  sym
    (ℝRing.-Swap·
      x
      (positiveReciprocal (- x)
        (negativeNegationPositive x<0)))
  ∙ positiveReciprocalLaw
      (- x)
      (negativeNegationPositive x<0)

inverseℝLaw' : ∀ x (p : 0 ＃ x) →
  inverseℝ x p · x ≡ 1
inverseℝLaw' x p =
  mulComm (inverseℝ x p) x
  ∙ inverseℝLaw x p

inverseℝApart : ∀ x (p : 0 ＃ x) →
  0 ＃ inverseℝ x p
inverseℝApart x (inl 0<x) =
  inl
    (positiveReciprocalPositive x 0<x)
inverseℝApart x (inr x<0) =
  inr
    (negationOfPositiveNegative
      (positiveReciprocalPositive
        (- x) (negativeNegationPositive x<0)))

inverseℝPositive : ∀ x (p : 0 ＃ x) →
  0 <ℝ x →
  0 <ℝ inverseℝ x p
inverseℝPositive x p 0<x =
  subst
    (0 <ℝ_)
    (sym
      (inverseℝProofIrrelevant
        x p (inl 0<x)))
    (positiveReciprocalPositive x 0<x)

inverseℝNegative : ∀ x (p : 0 ＃ x) →
  x <ℝ 0 →
  inverseℝ x p <ℝ 0
inverseℝNegative x p x<0 =
  subst
    (_<ℝ 0)
    (sym
      (inverseℝProofIrrelevant
        x p (inr x<0)))
    (negationOfPositiveNegative
      (positiveReciprocalPositive
        (- x) (negativeNegationPositive x<0)))

inverseℝUnique : ∀ x (p : 0 ＃ x) y →
  x · y ≡ 1 →
  y ≡ inverseℝ x p
inverseℝUnique x p y xy≡1 =
  sym (mulIdL y)
  ∙ cong (_· y) (sym (inverseℝLaw' x p))
  ∙ mulAssoc (inverseℝ x p) x y
  ∙ cong (inverseℝ x p ·_) xy≡1
  ∙ mulIdR (inverseℝ x p)

inverseℝInvolutive : ∀ x (p : 0 ＃ x) →
  inverseℝ
    (inverseℝ x p)
    (inverseℝApart x p)
  ≡ x
inverseℝInvolutive x p =
  sym
    (inverseℝUnique
      (inverseℝ x p)
      (inverseℝApart x p)
      x
      (inverseℝLaw' x p))

inverseℝOne : (p : 0 ＃ 1) →
  inverseℝ 1 p ≡ 1
inverseℝOne p =
  sym
    (inverseℝUnique 1 p 1 (mulIdL 1))

inverseℝ-rat : ∀ q
  (p : 0 ＃ rat q)
  (pℚ : 0 ℚ.# q) →
  inverseℝ (rat q) p ≡
  rat (ℚInv.invℚ q pℚ)
inverseℝ-rat q p pℚ =
  sym
    (inverseℝUnique
      (rat q) p
      (rat (ℚInv.invℚ q pℚ))
      (mul-rat q (ℚInv.invℚ q pℚ)
      ∙ cong rat (ℚInv.x·invℚ[x] q pℚ)))

inverseNegApart : ∀ x →
  0 ＃ x →
  0 ＃ (- x)
inverseNegApart x p =
  subst (_＃ (- x)) negZero
    (apartNeg 0 x p)

inverseℝNeg : ∀ x (p : 0 ＃ x) →
  inverseℝ (- x) (inverseNegApart x p) ≡
  - inverseℝ x p
inverseℝNeg x p =
  sym
    (inverseℝUnique
      (- x)
      (inverseNegApart x p)
      (- inverseℝ x p)
      (ℝRing.-Dist· x (inverseℝ x p)
      ∙ inverseℝLaw x p))

inverseℝMulWithProof : ∀ x y
  (px : 0 ＃ x) (py : 0 ＃ y) (pxy : 0 ＃ (x · y)) →
  inverseℝ (x · y) pxy ≡
  inverseℝ x px · inverseℝ y py
inverseℝMulWithProof x y px py pxy =
  sym
    (inverseℝUnique
      (x · y) pxy
      (inverseℝ x px · inverseℝ y py)
      productLaw)
  where
  productLaw :
    (x · y) · (inverseℝ x px · inverseℝ y py) ≡ 1
  productLaw =
    mulAssoc x y (inverseℝ x px · inverseℝ y py)
    ∙ cong (x ·_)
        (sym
          (mulAssoc y (inverseℝ x px) (inverseℝ y py)))
    ∙ cong (x ·_)
        (cong (_· inverseℝ y py)
          (mulComm y (inverseℝ x px)))
    ∙ cong (x ·_)
        (mulAssoc (inverseℝ x px) y (inverseℝ y py))
    ∙ sym
        (mulAssoc x (inverseℝ x px)
          (y · inverseℝ y py))
    ∙ cong₂ _·_
        (inverseℝLaw x px)
        (inverseℝLaw y py)
    ∙ mulIdR 1

inverseℝMul : ∀ x y (px : 0 ＃ x) (py : 0 ＃ y) →
  inverseℝ (x · y) (apartMul x y px py) ≡
  inverseℝ x px · inverseℝ y py
inverseℝMul x y px py =
  inverseℝMulWithProof
    x y px py (apartMul x y px py)

divideℝ : ℝ → (y : ℝ) → 0 ＃ y → ℝ
divideℝ x y p =
  x · inverseℝ y p

divideMulR : ∀ x y (p : 0 ＃ y) →
  divideℝ (x · y) y p ≡ x
divideMulR x y p =
  mulAssoc x y (inverseℝ y p)
  ∙ cong (x ·_) (inverseℝLaw y p)
  ∙ mulIdR x

mulDivideR : ∀ x y (p : 0 ＃ y) →
  divideℝ x y p · y ≡ x
mulDivideR x y p =
  mulAssoc x (inverseℝ y p) y
  ∙ cong (x ·_) (inverseℝLaw' y p)
  ∙ mulIdR x
