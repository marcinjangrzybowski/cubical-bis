module Cubical.Analysis.Real.Algebra.Inverse.Signed where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
import Cubical.Algebra.Ring.Properties as RingProperties

open import Cubical.Data.Rationals.Base
import Cubical.Data.Rationals.Inverse as ℚInv
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Sum as ⊎

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Order.Apartness
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.MultiplicativeApartness
open import Cubical.Analysis.Real.Algebra.Inverse.Positive
open import Cubical.Analysis.Real.Algebra.Inverse.Order


private
  module ℝRing = RingProperties.RingTheory (CommRing→Ring ℝCommRing)


inverseℝ : ∀ x → 0ℝ #ℝ x → ℝ
inverseℝ x (inl 0<x) = positiveReciprocal x 0<x
inverseℝ x (inr x<0) =
  - positiveReciprocal (- x)
      (negativeNegationPositive {x = x} x<0)


inverseℝProofIrrelevant : ∀ x
  (p q : 0ℝ #ℝ x) →
  inverseℝ x p ≡ inverseℝ x q
inverseℝProofIrrelevant x p q =
  cong (inverseℝ x) (isProp#ℝ 0ℝ x p q)


inverseℝLaw : ∀ x (p : 0ℝ #ℝ x) →
  x · inverseℝ x p ≡ 1ℝ
inverseℝLaw x (inl 0<x) = positiveReciprocalLaw x 0<x
inverseℝLaw x (inr x<0) =
    sym negativeProductPath
  ∙ positiveReciprocalLaw
      (- x) (negativeNegationPositive {x = x} x<0)
  where
  negativeProductPath :
    (- x) · positiveReciprocal (- x)
      (negativeNegationPositive {x = x} x<0)
    ≡
    x · (- positiveReciprocal (- x)
      (negativeNegationPositive {x = x} x<0))
  negativeProductPath =
    ℝRing.-Swap· x
      (positiveReciprocal (- x)
        (negativeNegationPositive {x = x} x<0))


inverseℝLaw' : ∀ x (p : 0ℝ #ℝ x) →
  inverseℝ x p · x ≡ 1ℝ
inverseℝLaw' x p =
  mulComm (inverseℝ x p) x ∙ inverseℝLaw x p


inverseℝApart : ∀ x (p : 0ℝ #ℝ x) →
  0ℝ #ℝ inverseℝ x p
inverseℝApart x (inl 0<x) =
  inl (positiveReciprocalPositive x 0<x)
inverseℝApart x (inr x<0) =
  inr
    (negationOfPositiveNegative
      (positiveReciprocalPositive
        (- x) (negativeNegationPositive {x = x} x<0)))


inverseℝPositive : ∀ x (p : 0ℝ #ℝ x) →
  0ℝ <ℝ x → 0ℝ <ℝ inverseℝ x p
inverseℝPositive x p 0<x =
  subst (0ℝ <ℝ_)
    (sym (inverseℝProofIrrelevant x p (inl 0<x)))
    (positiveReciprocalPositive x 0<x)


inverseℝNegative : ∀ x (p : 0ℝ #ℝ x) →
  x <ℝ 0ℝ → inverseℝ x p <ℝ 0ℝ
inverseℝNegative x p x<0 =
  subst (_<ℝ 0ℝ)
    (sym (inverseℝProofIrrelevant x p (inr x<0)))
    (negationOfPositiveNegative
      (positiveReciprocalPositive
        (- x) (negativeNegationPositive {x = x} x<0)))


inverseℝUnique : ∀ x (p : 0ℝ #ℝ x) y →
  x · y ≡ 1ℝ →
  y ≡ inverseℝ x p
inverseℝUnique x p y xy≡1 =
    sym (mulIdL y)
  ∙ cong (_· y) (sym (inverseℝLaw' x p))
  ∙ sym (mulAssoc (inverseℝ x p) x y)
  ∙ cong (inverseℝ x p ·_) xy≡1
  ∙ mulIdR (inverseℝ x p)


inverseℝInvolutive : ∀ x (p : 0ℝ #ℝ x) →
  inverseℝ (inverseℝ x p) (inverseℝApart x p) ≡ x
inverseℝInvolutive x p =
  sym
    (inverseℝUnique
      (inverseℝ x p) (inverseℝApart x p) x
      (inverseℝLaw' x p))


inverseℝOne : (p : 0ℝ #ℝ 1ℝ) →
  inverseℝ 1ℝ p ≡ 1ℝ
inverseℝOne p =
  sym (inverseℝUnique 1ℝ p 1ℝ (mulIdL 1ℝ))


inverseℝ-rat : ∀ q
  (p : 0ℝ #ℝ rat q)
  (pℚ : 0 ℚ.# q) →
  inverseℝ (rat q) p ≡ rat (ℚInv.invℚ q pℚ)
inverseℝ-rat q p pℚ =
  sym
    (inverseℝUnique
      (rat q) p
      (rat (ℚInv.invℚ q pℚ))
      (mul-rat q (ℚInv.invℚ q pℚ)
      ∙ cong rat (ℚInv.x·invℚ[x] q pℚ)))


inverseNegApart : ∀ x →
  0ℝ #ℝ x → 0ℝ #ℝ (- x)
inverseNegApart x p =
  subst (_#ℝ (- x)) negZero
    (apartNeg 0ℝ x p)


inverseℝNeg : ∀ x (p : 0ℝ #ℝ x) →
  inverseℝ (- x) (inverseNegApart x p) ≡ - inverseℝ x p
inverseℝNeg x p =
  sym
    (inverseℝUnique
      (- x) (inverseNegApart x p)
      (- inverseℝ x p)
      (negativeProductPath ∙ inverseℝLaw x p))
  where
  negativeProductPath :
    (- x) · (- inverseℝ x p) ≡ x · inverseℝ x p
  negativeProductPath = ℝRing.-Dist· x (inverseℝ x p)


inverseℝMulWithProof : ∀ x y
  (px : 0ℝ #ℝ x)
  (py : 0ℝ #ℝ y)
  (pxy : 0ℝ #ℝ (x · y)) →
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
    (x · y) · (inverseℝ x px · inverseℝ y py) ≡ 1ℝ
  productLaw =
      sym (mulAssoc x y (inverseℝ x px · inverseℝ y py))
    ∙ cong (x ·_)
        (mulAssoc y (inverseℝ x px) (inverseℝ y py))
    ∙ cong (λ value → x · (value · inverseℝ y py))
        (mulComm y (inverseℝ x px))
    ∙ cong (x ·_)
        (sym (mulAssoc (inverseℝ x px) y (inverseℝ y py)))
    ∙ mulAssoc x (inverseℝ x px)
        (y · inverseℝ y py)
    ∙ cong₂ _·_ (inverseℝLaw x px) (inverseℝLaw y py)
    ∙ mulIdL 1ℝ


inverseℝMul : ∀ x y
  (px : 0ℝ #ℝ x)
  (py : 0ℝ #ℝ y) →
  inverseℝ (x · y) (apartMul x y px py) ≡
  inverseℝ x px · inverseℝ y py
inverseℝMul x y px py =
  inverseℝMulWithProof x y px py (apartMul x y px py)


divideℝ : ℝ → (y : ℝ) → 0ℝ #ℝ y → ℝ
divideℝ x y p = x · inverseℝ y p


divideMulRight : ∀ x y (p : 0ℝ #ℝ y) →
  divideℝ (x · y) y p ≡ x
divideMulRight x y p =
    sym (mulAssoc x y (inverseℝ y p))
  ∙ cong (x ·_) (inverseℝLaw y p)
  ∙ mulIdR x


mulDivideRight : ∀ x y (p : 0ℝ #ℝ y) →
  divideℝ x y p · y ≡ x
mulDivideRight x y p =
    sym (mulAssoc x (inverseℝ y p) y)
  ∙ cong (x ·_) (inverseℝLaw' y p)
  ∙ mulIdR x


opaque
  mul-cancel-right-apart : ∀ x y z →
    (z-apart : 0ℝ #ℝ z) →
    x · z ≡ y · z → x ≡ y
  mul-cancel-right-apart x y z z-apart products-equal =
      sym (mulIdR x)
    ∙ cong (x ·_) (sym (inverseℝLaw z z-apart))
    ∙ mulAssoc x z (inverseℝ z z-apart)
    ∙ cong (_· inverseℝ z z-apart) products-equal
    ∙ sym (mulAssoc y z (inverseℝ z z-apart))
    ∙ cong (y ·_) (inverseℝLaw z z-apart)
    ∙ mulIdR y

  mul-cancel-left-apart : ∀ x y z →
    (z-apart : 0ℝ #ℝ z) →
    z · x ≡ z · y → x ≡ y
  mul-cancel-left-apart x y z z-apart products-equal =
    mul-cancel-right-apart x y z z-apart
      (mulComm x z ∙ products-equal ∙ mulComm z y)


opaque
  apartMul-reflects-right : ∀ x y →
    (x-apart : 0ℝ #ℝ x) →
    0ℝ #ℝ (x · y) →
    0ℝ #ℝ y
  apartMul-reflects-right x y x-apart product-apart =
    subst
      (0ℝ #ℝ_)
      divided-product
      (apartMul
        (inverseℝ x x-apart) (x · y)
        (inverseℝApart x x-apart) product-apart)
    where
    divided-product :
      inverseℝ x x-apart · (x · y) ≡ y
    divided-product =
        mulAssoc (inverseℝ x x-apart) x y
      ∙ cong (_· y) (inverseℝLaw' x x-apart)
      ∙ mulIdL y

  apartMul-reflects-left : ∀ x y →
    (y-apart : 0ℝ #ℝ y) →
    0ℝ #ℝ (x · y) →
    0ℝ #ℝ x
  apartMul-reflects-left x y y-apart product-apart =
    apartMul-reflects-right y x y-apart
      (subst
        (0ℝ #ℝ_)
        (mulComm x y)
        product-apart)
