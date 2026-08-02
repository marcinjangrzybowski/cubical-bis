module Cubical.HITs.CauchyRealsP.Algebra.Order.Addition where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra.Addition
open import Cubical.HITs.CauchyRealsP.Algebra.AdditionLaws
open import Cubical.HITs.CauchyRealsP.Algebra.Negation
open import Cubical.HITs.CauchyRealsP.Algebra.AdditiveGroup
open import Cubical.HITs.CauchyRealsP.Algebra.AdditiveGroupLaws
open import Cubical.HITs.CauchyRealsP.Algebra.Lattice
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Base

open import Cubical.Relation.Premetric.Mappings

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

private
  composeIsNonExpanding :
    (f g : ℝ → ℝ)
    → IsNonExpanding (snd ℝPremetricSpace) f (snd ℝPremetricSpace)
    → IsNonExpanding (snd ℝPremetricSpace) g (snd ℝPremetricSpace)
    → IsNonExpanding (snd ℝPremetricSpace) (f ∘ g)
        (snd ℝPremetricSpace)
  composeIsNonExpanding f g f-ne g-ne
    .IsNonExpanding.pres≈ x y ε x∼y =
      IsNonExpanding.pres≈ f-ne (g x) (g y) ε
        (IsNonExpanding.pres≈ g-ne x y ε x∼y)

  maxTranslateIsLipschitzWith2 : ∀ x y →
    IsLipschitzWith
      (snd ℝPremetricSpace)
      (λ z → maxℝ (x + z) (y + z))
      (snd ℝPremetricSpace) 2
  maxTranslateIsLipschitzWith2 x y
    .IsLipschitzWith.pres≈ z z' ε z∼z' =
      subst∼
        (maxℝ (x + z) (y + z))
        (maxℝ (x + z') (y + z'))
        {ε = ε +₊ ε} {ε' = 2 ·₊ ε}
        ℚ!
        (maxPres∼
          (x + z) (x + z')
          (y + z) (y + z')
          ε ε
          (addPres∼₂ x z z' ε z∼z')
          (addPres∼₂ y z z' ε z∼z'))

maxAddDistribR : ∀ x y z →
  maxℝ x y + z ≡ maxℝ (x + z) (y + z)
maxAddDistribR x y z =
  funExt⁻
    (nonExpandingExtensionality ℝPremetricSpace
      (λ u → maxℝ u y + z)
      (λ u → maxℝ (u + z) (y + z))
      (composeIsNonExpanding
        (_+ z) (λ u → maxℝ u y)
        (addIsNonExpanding₁ z) (maxIsNonExpanding₁ y))
      (composeIsNonExpanding
        (λ u → maxℝ u (y + z)) (_+ z)
        (maxIsNonExpanding₁ (y + z)) (addIsNonExpanding₁ z))
      λ p →
        funExt⁻
          (nonExpandingExtensionality ℝPremetricSpace
            (λ v → maxℝ (rat p) v + z)
            (λ v → maxℝ (rat p + z) (v + z))
            (composeIsNonExpanding
              (_+ z) (maxℝ (rat p))
              (addIsNonExpanding₁ z)
              (maxIsNonExpanding₂ (rat p)))
            (composeIsNonExpanding
              (maxℝ (rat p + z)) (_+ z)
              (maxIsNonExpanding₂ (rat p + z))
              (addIsNonExpanding₁ z))
            λ q →
              funExt⁻
                (lipschitzExtensionality ℝPremetricSpace
                  (λ w → maxℝ (rat p) (rat q) + w)
                  (λ w → maxℝ (rat p + w) (rat q + w))
                  (isNonExpanding→isLipschitz
                    (snd ℝPremetricSpace) _
                    (snd ℝPremetricSpace)
                    (addIsNonExpanding₂ (maxℝ (rat p) (rat q))))
                  ∣ 2 , maxTranslateIsLipschitzWith2
                    (rat p) (rat q) ∣₁
                  λ r →
                    cong (_+ rat r) (max-rat p q)
                    ∙ rat+rat (ℚ.max p q) r
                    ∙ cong rat (ℚ.+MaxDistrℚ p q r)
                    ∙ sym (max-rat (p ℚ.+ r) (q ℚ.+ r))
                    ∙ cong₂ maxℝ
                        (sym (rat+rat p r))
                        (sym (rat+rat q r)))
                z)
          y)
    x

maxAddDistribL : ∀ x y z →
  z + maxℝ x y ≡ maxℝ (z + x) (z + y)
maxAddDistribL x y z =
  addComm z (maxℝ x y)
  ∙ maxAddDistribR x y z
  ∙ cong₂ maxℝ (addComm x z) (addComm y z)

opaque
  unfolding _≤ℝ_

  ≤ℝ-addR : ∀ x y z → x ≤ℝ y → x + z ≤ℝ y + z
  ≤ℝ-addR x y z x≤y =
    sym (maxAddDistribR x y z)
    ∙ cong (_+ z) x≤y

≤ℝ-addL : ∀ x y z → x ≤ℝ y → z + x ≤ℝ z + y
≤ℝ-addL x y z =
  subst2 _≤ℝ_ (addComm x z) (addComm y z)
  ∘ ≤ℝ-addR x y z

≤ℝ-add : ∀ x y z w →
  x ≤ℝ y → z ≤ℝ w → x + z ≤ℝ y + w
≤ℝ-add x y z w x≤y z≤w =
  ≤ℝ-trans (x + z) (y + z) (y + w)
    (≤ℝ-addR x y z x≤y)
    (≤ℝ-addL z w y z≤w)

≤ℝ-neg : ∀ x y → x ≤ℝ y → (- y) ≤ℝ (- x)
≤ℝ-neg x y x≤y =
  subst2 _≤ℝ_
    (addAssoc x (- x) (- y)
      ∙ cong (_+ (- y)) (addInvR x)
      ∙ addIdL (- y))
    (cong (y +_) (addComm (- x) (- y))
      ∙ addAssoc y (- y) (- x)
      ∙ cong (_+ (- x)) (addInvR y)
      ∙ addIdL (- x))
    (≤ℝ-addR x y ((- x) + (- y)) x≤y)

neg≤ℝ : ∀ x y → (- y) ≤ℝ (- x) → x ≤ℝ y
neg≤ℝ x y =
  subst2 _≤ℝ_ (negInvol x) (negInvol y)
  ∘ ≤ℝ-neg (- y) (- x)

≤ℝ-addR-cancel : ∀ x y z → x + z ≤ℝ y + z → x ≤ℝ y
≤ℝ-addR-cancel x y z =
  subst2 _≤ℝ_
    (addSubCancel x z)
    (addSubCancel y z)
  ∘ ≤ℝ-addR (x + z) (y + z) (- z)

≤ℝ-addL-cancel : ∀ x y z → z + x ≤ℝ z + y → x ≤ℝ y
≤ℝ-addL-cancel x y z =
  ≤ℝ-addR-cancel x y z
  ∘ subst2 _≤ℝ_ (addComm z x) (addComm z y)

addR≤Equiv : ∀ x y z → (x + z ≤ℝ y + z) ≃ (x ≤ℝ y)
addR≤Equiv x y z =
  propBiimpl→Equiv
    {A = x + z ≤ℝ y + z} {B = x ≤ℝ y}
    (isProp≤ℝ (x + z) (y + z)) (isProp≤ℝ x y)
    (≤ℝ-addR-cancel x y z) (≤ℝ-addR x y z)

nonnegativeSub : ∀ x y →
  x ≤ℝ y → 0 ≤ℝ y - x
nonnegativeSub x y x≤y =
  subst
    (_≤ℝ y - x)
    (subSelf x)
    (≤ℝ-addR x y (- x) x≤y)

nonnegativeSub→≤ : ∀ x y →
  0 ≤ℝ y - x → x ≤ℝ y
nonnegativeSub→≤ x y 0≤y-x =
  subst2 _≤ℝ_
    (addIdL x)
    (subAddCancel y x)
    (≤ℝ-addR 0 (y - x) x 0≤y-x)

min≤left : ∀ x y → minℝ x y ≤ℝ x
min≤left x y =
  subst2 _≤ℝ_
    refl
    (negInvol x)
    (≤ℝ-neg (- x) (maxℝ (- x) (- y))
      (left≤max (- x) (- y)))

min≤right : ∀ x y → minℝ x y ≤ℝ y
min≤right x y =
  subst2 _≤ℝ_
    refl
    (negInvol y)
    (≤ℝ-neg (- y) (maxℝ (- x) (- y))
      (right≤max (- x) (- y)))

≤min : ∀ z x y → z ≤ℝ x → z ≤ℝ y → z ≤ℝ minℝ x y
≤min z x y z≤x z≤y =
  subst2 _≤ℝ_
    (negInvol z)
    refl
    (≤ℝ-neg
      (maxℝ (- x) (- y)) (- z)
      (max≤
        (- x) (- y) (- z)
        (≤ℝ-neg z x z≤x)
        (≤ℝ-neg z y z≤y)))

minOf≤ : ∀ x y → x ≤ℝ y → minℝ x y ≡ x
minOf≤ x y x≤y =
  ≤ℝ-antisym
    (minℝ x y) x
    (min≤left x y)
    (≤min x x y (≤ℝ-refl x) x≤y)
