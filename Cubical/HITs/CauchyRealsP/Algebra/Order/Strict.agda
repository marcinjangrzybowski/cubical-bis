module Cubical.HITs.CauchyRealsP.Algebra.Order.Strict where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function

open import Cubical.Data.Empty as ⊥
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary.Order.Quoset

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra.Addition
open import Cubical.HITs.CauchyRealsP.Algebra.AdditionLaws
open import Cubical.HITs.CauchyRealsP.Algebra.Negation
open import Cubical.HITs.CauchyRealsP.Algebra.AdditiveGroup
open import Cubical.HITs.CauchyRealsP.Algebra.AdditiveGroupLaws
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Base
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Addition

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

infix 4 _<ℝ_

opaque
  GapBound : ℝ → ℝ → ℚ₊ → Type
  GapBound x y δ = x + rat (fst δ) ≤ℝ y

  gapBoundIntro : ∀ x y δ →
    x + rat (fst δ) ≤ℝ y → GapBound x y δ
  gapBoundIntro _ _ _ p = p

  gapBoundElim : ∀ x y δ →
    GapBound x y δ → x + rat (fst δ) ≤ℝ y
  gapBoundElim _ _ _ p = p

record PositiveGap (x y : ℝ) : Type where
  constructor positiveGap
  field
    width : ℚ₊
    bound : GapBound x y width

open PositiveGap public

_<ℝ_ : ℝ → ℝ → Type
x <ℝ y = ∥ PositiveGap x y ∥₁

isProp<ℝ : ∀ x y → isProp (x <ℝ y)
isProp<ℝ _ _ = squash₁

private
  combineGapPath : ∀ x (δ ε : ℚ₊) →
    x + rat (fst (δ +₊ ε)) ≡
    (x + rat (fst δ)) + rat (fst ε)
  combineGapPath x δ ε =
    cong (x +_) (sym (rat+rat (fst δ) (fst ε)))
    ∙ addAssoc x (rat (fst δ)) (rat (fst ε))

  translateGapRPath : ∀ x z q →
    (x + z) + rat q ≡ (x + rat q) + z
  translateGapRPath x z q =
    sym (addAssoc x z (rat q))
    ∙ cong (x +_) (addComm z (rat q))
    ∙ addAssoc x (rat q) z

<ℚ→<ℝ : ∀ p q → p ℚ.< q → rat p <ℝ rat q
<ℚ→<ℝ p q p<q =
  ∣ positiveGap δ
      (gapBoundIntro (rat p) (rat q) δ
        (subst (_≤ℝ rat q) (sym gapEq) (≤ℝ-refl (rat q)))) ∣₁
  where
  δ : ℚ₊
  δ = ℚ.<→ℚ₊ p q p<q

  gapEq : rat p + rat (fst δ) ≡ rat q
  gapEq =
    rat+rat p (fst δ)
    ∙ cong rat ℚ!

<ℝ→<ℚ : ∀ p q → rat p <ℝ rat q → p ℚ.< q
<ℝ→<ℚ p q =
  PT.rec (ℚ.isProp< p q) λ w →
    let
      p<p+width : p ℚ.< p ℚ.+ fst (width w)
      p<p+width =
        subst (ℚ._< (p ℚ.+ fst (width w)))
          (ℚ.+IdR p)
          (ℚ.<-o+ 0 (fst (width w)) p (snd (width w)))
    in
      ℚ.isTrans<≤ p (p ℚ.+ fst (width w)) q
        p<p+width
        (≤ℝ→≤ℚ (p ℚ.+ fst (width w)) q
          (subst (_≤ℝ rat q)
            (rat+rat p (fst (width w)))
            (gapBoundElim
              (rat p) (rat q) (width w) (bound w))))

<ratEquiv : ∀ p q → (rat p <ℝ rat q) ≃ (p ℚ.< q)
<ratEquiv p q =
  propBiimpl→Equiv
    {A = rat p <ℝ rat q} {B = p ℚ.< q}
    (isProp<ℝ (rat p) (rat q)) (ℚ.isProp< p q)
    (<ℝ→<ℚ p q) (<ℚ→<ℝ p q)

<ℝ-trans : ∀ x y z → x <ℝ y → y <ℝ z → x <ℝ z
<ℝ-trans x y z =
  PT.map2 λ u v →
    positiveGap (width u +₊ width v)
      (gapBoundIntro x z (width u +₊ width v)
        (subst (_≤ℝ z) (sym (combineGapPath x (width u) (width v)))
          (≤ℝ-trans
            ((x + rat (fst (width u))) + rat (fst (width v)))
            (y + rat (fst (width v)))
            z
            (≤ℝ-addR
              (x + rat (fst (width u))) y
              (rat (fst (width v)))
              (gapBoundElim x y (width u) (bound u)))
            (gapBoundElim y z (width v) (bound v)))))

≤<ℝ-trans : ∀ x y z → x ≤ℝ y → y <ℝ z → x <ℝ z
≤<ℝ-trans x y z x≤y =
  PT.map λ w →
    positiveGap (width w)
      (gapBoundIntro x z (width w)
        (≤ℝ-trans
          (x + rat (fst (width w)))
          (y + rat (fst (width w)))
          z
          (≤ℝ-addR x y (rat (fst (width w))) x≤y)
          (gapBoundElim y z (width w) (bound w))))

<≤ℝ-trans : ∀ x y z → x <ℝ y → y ≤ℝ z → x <ℝ z
<≤ℝ-trans x y z x<y y≤z =
  PT.map
    (λ w →
      positiveGap (width w)
        (gapBoundIntro x z (width w)
          (≤ℝ-trans
            (x + rat (fst (width w))) y z
            (gapBoundElim x y (width w) (bound w))
            y≤z)))
    x<y

<ℝ-weaken : ∀ x y → x <ℝ y → x ≤ℝ y
<ℝ-weaken x y =
  PT.rec (isProp≤ℝ x y) λ w →
    ≤ℝ-trans x (x + rat (fst (width w))) y
      (subst (_≤ℝ (x + rat (fst (width w))))
        (addIdR x)
        (≤ℝ-addL
          (rat 0) (rat (fst (width w))) x
          (≤ℚ→≤ℝ 0 (fst (width w))
            (ℚ.<Weaken≤ 0 (fst (width w)) (snd (width w))))))
      (gapBoundElim x y (width w) (bound w))

<ℝ-irrefl : ∀ x → ¬ x <ℝ x
<ℝ-irrefl x =
  PT.rec isProp⊥ λ w →
    ℚ.isIrrefl< 0
      (ℚ.isTrans<≤ 0 (fst (width w)) 0
        (snd (width w))
        (≤ℝ→≤ℚ (fst (width w)) 0
          (≤ℝ-addL-cancel
            (rat (fst (width w))) (rat 0) x
            (subst ((x + rat (fst (width w))) ≤ℝ_)
              (sym (addIdR x))
              (gapBoundElim x x (width w) (bound w))))))

<ℝ-asym : ∀ x y → x <ℝ y → y <ℝ x → ⊥
<ℝ-asym x y x<y y<x =
  <ℝ-irrefl x (<ℝ-trans x y x x<y y<x)

<ℝ-addR : ∀ x y z → x <ℝ y → x + z <ℝ y + z
<ℝ-addR x y z =
  PT.map λ w →
    positiveGap (width w)
      (gapBoundIntro (x + z) (y + z) (width w)
        (subst (_≤ℝ (y + z))
          (sym (translateGapRPath x z (fst (width w))))
          (≤ℝ-addR
            (x + rat (fst (width w))) y z
            (gapBoundElim x y (width w) (bound w)))))

<ℝ-addL : ∀ x y z → x <ℝ y → z + x <ℝ z + y
<ℝ-addL x y z =
  subst2 _<ℝ_ (addComm x z) (addComm y z)
  ∘ <ℝ-addR x y z

<ℝ-add : ∀ x y z w →
  x <ℝ y → z <ℝ w → x + z <ℝ y + w
<ℝ-add x y z w x<y z<w =
  <ℝ-trans (x + z) (y + z) (y + w)
    (<ℝ-addR x y z x<y)
    (<ℝ-addL z w y z<w)

≤<ℝ-add : ∀ x y z w →
  x ≤ℝ y → z <ℝ w → x + z <ℝ y + w
≤<ℝ-add x y z w x≤y z<w =
  ≤<ℝ-trans (x + z) (y + z) (y + w)
    (≤ℝ-addR x y z x≤y)
    (<ℝ-addL z w y z<w)

<≤ℝ-add : ∀ x y z w →
  x <ℝ y → z ≤ℝ w → x + z <ℝ y + w
<≤ℝ-add x y z w x<y z≤w =
  <≤ℝ-trans (x + z) (y + z) (y + w)
    (<ℝ-addR x y z x<y)
    (≤ℝ-addL z w y z≤w)

<ℝ-addR-cancel : ∀ x y z → x + z <ℝ y + z → x <ℝ y
<ℝ-addR-cancel x y z =
  subst2 _<ℝ_ (addSubCancel x z) (addSubCancel y z)
  ∘ <ℝ-addR (x + z) (y + z) (- z)

<ℝ-addL-cancel : ∀ x y z → z + x <ℝ z + y → x <ℝ y
<ℝ-addL-cancel x y z =
  <ℝ-addR-cancel x y z
  ∘ subst2 _<ℝ_ (addComm z x) (addComm z y)

addR<Equiv : ∀ x y z → (x + z <ℝ y + z) ≃ (x <ℝ y)
addR<Equiv x y z =
  propBiimpl→Equiv
    {A = x + z <ℝ y + z} {B = x <ℝ y}
    (isProp<ℝ (x + z) (y + z)) (isProp<ℝ x y)
    (<ℝ-addR-cancel x y z) (<ℝ-addR x y z)

positiveSub : ∀ x y →
  x <ℝ y → 0 <ℝ y - x
positiveSub x y x<y =
  subst2 _<ℝ_
    (subSelf x)
    refl
    (<ℝ-addR x y (- x) x<y)

positiveSub→< : ∀ x y →
  0 <ℝ y - x → x <ℝ y
positiveSub→< x y 0<y-x =
  subst2 _<ℝ_
    (addIdL x)
    (subAddCancel y x)
    (<ℝ-addR 0 (y - x) x 0<y-x)

<ℝ-neg : ∀ x y → x <ℝ y → (- y) <ℝ (- x)
<ℝ-neg x y x<y =
  subst2 _<ℝ_
    (addAssoc x (- x) (- y)
      ∙ cong (_+ (- y)) (addInvR x)
      ∙ addIdL (- y))
    (cong (y +_) (addComm (- x) (- y))
      ∙ addAssoc y (- y) (- x)
      ∙ cong (_+ (- x)) (addInvR y)
      ∙ addIdL (- x))
    (<ℝ-addR x y ((- x) + (- y)) x<y)

neg<ℝ : ∀ x y → (- y) <ℝ (- x) → x <ℝ y
neg<ℝ x y =
  subst2 _<ℝ_ (negInvol x) (negInvol y)
  ∘ <ℝ-neg (- y) (- x)

isQuosetℝ : IsQuoset _<ℝ_
isQuosetℝ .IsQuoset.is-set = isSetℝ
isQuosetℝ .IsQuoset.is-prop-valued = isProp<ℝ
isQuosetℝ .IsQuoset.is-irrefl = <ℝ-irrefl
isQuosetℝ .IsQuoset.is-trans = <ℝ-trans
isQuosetℝ .IsQuoset.is-asym = <ℝ-asym

ℝ<Quoset : Quoset ℓ-zero ℓ-zero
ℝ<Quoset = quoset ℝ _<ℝ_ isQuosetℝ
