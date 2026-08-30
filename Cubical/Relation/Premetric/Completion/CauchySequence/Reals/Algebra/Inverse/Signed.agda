module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Inverse.Signed where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring

open import Cubical.Data.Rationals.Base
import Cubical.Data.Rationals.Inverse as ℚInv
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Sum as ⊎

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.GroupLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Associativity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Apartness
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.MultiplicativeApartness
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Properties
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Inverse.Positive
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Inverse.Order


private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)

  rearrangeFourFactors : ∀ (a b c d : Real.ℝ) →
    (a Mul.· b) Mul.· (c Mul.· d)
      ≡
    (a Mul.· c) Mul.· (b Mul.· d)
  rearrangeFourFactors a b c d =
      sym (mul-assoc a b (c Mul.· d))
    ∙ cong (a Mul.·_)
        (mul-assoc b c d)
    ∙ cong (λ value → a Mul.· (value Mul.· d))
        (mul-comm b c)
    ∙ cong (a Mul.·_)
        (sym (mul-assoc c b d))
    ∙ mul-assoc a c (b Mul.· d)


negativeNegationPositive : ∀ {x} →
  x <ℝ Real.ιℚ 0 → Real.ιℚ 0 <ℝ (Neg.- x)
negativeNegationPositive {x} x<0 =
  subst2 _<ℝ_ neg-zero refl
    (<ℝ-neg x (Real.ιℚ 0) x<0)


inverseℝ : ∀ x → Real.ιℚ 0 ＃ x → Real.ℝ
inverseℝ x (inl 0<x) = positiveReciprocal x 0<x
inverseℝ x (inr x<0) =
  Neg.- positiveReciprocal (Neg.- x) (negativeNegationPositive x<0)


inverseℝProofIrrelevant : ∀ x
  (p q : Real.ιℚ 0 ＃ x) →
  inverseℝ x p ≡ inverseℝ x q
inverseℝProofIrrelevant x p q =
  cong (inverseℝ x) (isProp＃ (Real.ιℚ 0) x p q)


inverseℝLaw : ∀ x (p : Real.ιℚ 0 ＃ x) →
  x Mul.· inverseℝ x p ≡ Real.ιℚ 1
inverseℝLaw x (inl 0<x) = positiveReciprocalLaw x 0<x
inverseℝLaw x (inr x<0) =
    sym
      (ℝRing.-Swap· x
        (positiveReciprocal (Neg.- x)
          (negativeNegationPositive x<0)))
  ∙ positiveReciprocalLaw
      (Neg.- x) (negativeNegationPositive x<0)


inverseℝLaw' : ∀ x (p : Real.ιℚ 0 ＃ x) →
  inverseℝ x p Mul.· x ≡ Real.ιℚ 1
inverseℝLaw' x p =
  mul-comm (inverseℝ x p) x ∙ inverseℝLaw x p


negationOfPositiveNegative : ∀ {x} →
  Real.ιℚ 0 <ℝ x → Neg.- x <ℝ Real.ιℚ 0
negationOfPositiveNegative {x} 0<x =
  subst ((Neg.- x) <ℝ_) neg-zero
    (<ℝ-neg (Real.ιℚ 0) x 0<x)


inverseℝApart : ∀ x (p : Real.ιℚ 0 ＃ x) →
  Real.ιℚ 0 ＃ inverseℝ x p
inverseℝApart x (inl 0<x) =
  inl (positiveReciprocalPositive x 0<x)
inverseℝApart x (inr x<0) =
  inr
    (negationOfPositiveNegative
      (positiveReciprocalPositive
        (Neg.- x) (negativeNegationPositive x<0)))


inverseℝPositive : ∀ x (p : Real.ιℚ 0 ＃ x) →
  Real.ιℚ 0 <ℝ x → Real.ιℚ 0 <ℝ inverseℝ x p
inverseℝPositive x p 0<x =
  subst (Real.ιℚ 0 <ℝ_)
    (sym (inverseℝProofIrrelevant x p (inl 0<x)))
    (positiveReciprocalPositive x 0<x)


inverseℝNegative : ∀ x (p : Real.ιℚ 0 ＃ x) →
  x <ℝ Real.ιℚ 0 → inverseℝ x p <ℝ Real.ιℚ 0
inverseℝNegative x p x<0 =
  subst (_<ℝ Real.ιℚ 0)
    (sym (inverseℝProofIrrelevant x p (inr x<0)))
    (negationOfPositiveNegative
      (positiveReciprocalPositive
        (Neg.- x) (negativeNegationPositive x<0)))


inverseℝUnique : ∀ x (p : Real.ιℚ 0 ＃ x) y →
  x Mul.· y ≡ Real.ιℚ 1 → y ≡ inverseℝ x p
inverseℝUnique x p y xy≡1 =
    sym (mul-one-left y)
  ∙ cong (Mul._· y) (sym (inverseℝLaw' x p))
  ∙ sym (mul-assoc (inverseℝ x p) x y)
  ∙ cong (inverseℝ x p Mul.·_) xy≡1
  ∙ mul-one-right (inverseℝ x p)


-- Multiplicativity is stated using the canonical apartness proof produced
-- by `apartMul`; proof irrelevance then makes it usable with any other proof
-- of apartness of the product.

inverseℝMul : ∀ x y
  (px : Real.ιℚ 0 ＃ x)
  (py : Real.ιℚ 0 ＃ y) →
  inverseℝ (x Mul.· y) (apartMul x y px py)
    ≡
  inverseℝ x px Mul.· inverseℝ y py
inverseℝMul x y px py =
  sym
    (inverseℝUnique
      (x Mul.· y)
      (apartMul x y px py)
      (inverseℝ x px Mul.· inverseℝ y py)
      product-law)
  where
  product-law :
    (x Mul.· y) Mul.·
        (inverseℝ x px Mul.· inverseℝ y py)
      ≡
    Real.ιℚ 1
  product-law =
      rearrangeFourFactors
        x y (inverseℝ x px) (inverseℝ y py)
    ∙ cong₂ Mul._·_ (inverseℝLaw x px) (inverseℝLaw y py)
    ∙ mul-one-left (Real.ιℚ 1)


inverseℝInvolutive : ∀ x (p : Real.ιℚ 0 ＃ x) →
  inverseℝ (inverseℝ x p) (inverseℝApart x p) ≡ x
inverseℝInvolutive x p =
  sym
    (inverseℝUnique
      (inverseℝ x p) (inverseℝApart x p) x
      (inverseℝLaw' x p))


inverseℝOne : (p : Real.ιℚ 0 ＃ Real.ιℚ 1) →
  inverseℝ (Real.ιℚ 1) p ≡ Real.ιℚ 1
inverseℝOne p =
  sym (inverseℝUnique
    (Real.ιℚ 1) p (Real.ιℚ 1)
    (mul-one-left (Real.ιℚ 1)))


inverseℝ-ι : ∀ q
  (p : Real.ιℚ 0 ＃ Real.ιℚ q)
  (pℚ : 0 ℚ.# q) →
  inverseℝ (Real.ιℚ q) p ≡
  Real.ιℚ (ℚInv.invℚ q pℚ)
inverseℝ-ι q p pℚ =
  sym
    (inverseℝUnique
      (Real.ιℚ q) p
      (Real.ιℚ (ℚInv.invℚ q pℚ))
      (Mul.mul-ι-ι q (ℚInv.invℚ q pℚ)
      ∙ cong Real.ιℚ (ℚInv.x·invℚ[x] q pℚ)))


inverseNegApart : ∀ x →
  Real.ιℚ 0 ＃ x → Real.ιℚ 0 ＃ (Neg.- x)
inverseNegApart x p =
  subst (_＃ (Neg.- x)) neg-zero
    (apart-neg (Real.ιℚ 0) x p)


inverseℝNeg : ∀ x (p : Real.ιℚ 0 ＃ x) →
  inverseℝ (Neg.- x) (inverseNegApart x p) ≡ Neg.- inverseℝ x p
inverseℝNeg x p =
  sym
    (inverseℝUnique
      (Neg.- x) (inverseNegApart x p)
      (Neg.- inverseℝ x p)
      (ℝRing.-Dist· x (inverseℝ x p)
      ∙ inverseℝLaw x p))


divideℝ : Real.ℝ → (y : Real.ℝ) →
  Real.ιℚ 0 ＃ y → Real.ℝ
divideℝ x y p = x Mul.· inverseℝ y p


divideMulRight : ∀ x y (p : Real.ιℚ 0 ＃ y) →
  divideℝ (x Mul.· y) y p ≡ x
divideMulRight x y p =
    sym (mul-assoc x y (inverseℝ y p))
  ∙ cong (x Mul.·_) (inverseℝLaw y p)
  ∙ mul-one-right x


mulDivideRight : ∀ x y (p : Real.ιℚ 0 ＃ y) →
  divideℝ x y p Mul.· y ≡ x
mulDivideRight x y p =
    sym (mul-assoc x (inverseℝ y p) y)
  ∙ cong (x Mul.·_) (inverseℝLaw' y p)
  ∙ mul-one-right x


-- Multiplication by an apart factor is cancellable.  These laws are stated
-- here, after signed inversion has been constructed, rather than requiring
-- integral-domain structure from the completed ring.

opaque
  mul-cancel-right-apart : ∀ x y z →
    (z-apart : Real.ιℚ 0 ＃ z) →
    x Mul.· z ≡ y Mul.· z → x ≡ y
  mul-cancel-right-apart x y z z-apart products-equal =
      sym (mul-one-right x)
    ∙ cong (x Mul.·_) (sym (inverseℝLaw z z-apart))
    ∙ mul-assoc x z (inverseℝ z z-apart)
    ∙ cong (Mul._· inverseℝ z z-apart) products-equal
    ∙ sym (mul-assoc y z (inverseℝ z z-apart))
    ∙ cong (y Mul.·_) (inverseℝLaw z z-apart)
    ∙ mul-one-right y


  mul-cancel-left-apart : ∀ x y z →
    (z-apart : Real.ιℚ 0 ＃ z) →
    z Mul.· x ≡ z Mul.· y → x ≡ y
  mul-cancel-left-apart x y z z-apart products-equal =
    mul-cancel-right-apart x y z z-apart
      ( mul-comm x z
      ∙ products-equal
      ∙ mul-comm z y)


-- Apartness of a product reflects to either factor once the other factor is
-- already known apart.  The proof explicitly divides out that factor, so it
-- retains the rational gap carried by constructive apartness.

opaque
  apartMul-reflects-right : ∀ x y →
    (x-apart : Real.ιℚ 0 ＃ x) →
    Real.ιℚ 0 ＃ (x Mul.· y) →
    Real.ιℚ 0 ＃ y
  apartMul-reflects-right x y x-apart product-apart =
    subst
      (Real.ιℚ 0 ＃_)
      divided-product
      (apartMul
        (inverseℝ x x-apart) (x Mul.· y)
        (inverseℝApart x x-apart) product-apart)
    where
    divided-product :
      inverseℝ x x-apart Mul.· (x Mul.· y) ≡ y
    divided-product =
        mul-assoc (inverseℝ x x-apart) x y
      ∙ cong (Mul._· y) (inverseℝLaw' x x-apart)
      ∙ mul-one-left y


  apartMul-reflects-left : ∀ x y →
    (y-apart : Real.ιℚ 0 ＃ y) →
    Real.ιℚ 0 ＃ (x Mul.· y) →
    Real.ιℚ 0 ＃ x
  apartMul-reflects-left x y y-apart product-apart =
    apartMul-reflects-right y x y-apart
      (subst
        (Real.ιℚ 0 ＃_)
        (mul-comm x y)
        product-apart)
