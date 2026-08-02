module Cubical.HITs.CauchyRealsP.Algebra.Order.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function

open import Cubical.Relation.Binary.Order.Poset

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra.Lattice

infix 4 _≤ℝ_

opaque
  _≤ℝ_ : ℝ → ℝ → Type
  x ≤ℝ y = maxℝ x y ≡ y

  isProp≤ℝ : ∀ x y → isProp (x ≤ℝ y)
  isProp≤ℝ x y = isSetℝ (maxℝ x y) y

  ≤ℝ-refl : ∀ x → x ≤ℝ x
  ≤ℝ-refl = maxIdem

  ≤ℝ-antisym : ∀ x y → x ≤ℝ y → y ≤ℝ x → x ≡ y
  ≤ℝ-antisym x y x≤y y≤x =
    sym y≤x
    ∙ maxComm y x
    ∙ x≤y

  ≤ℝ-trans : ∀ x y z → x ≤ℝ y → y ≤ℝ z → x ≤ℝ z
  ≤ℝ-trans x y z x≤y y≤z =
    cong (maxℝ x) (sym y≤z)
    ∙ maxAssoc x y z
    ∙ cong (λ u → maxℝ u z) x≤y
    ∙ y≤z

  ≤ℚ→≤ℝ : ∀ p q → p ℚ.≤ q → rat p ≤ℝ rat q
  ≤ℚ→≤ℝ p q p≤q =
    max-rat p q
    ∙ ratMax≡ratQ
    where
    ratMax≡ratQ : rat (ℚ.max p q) ≡ rat q
    ratMax≡ratQ = cong rat (ℚ.≤→max p q p≤q)

  ≤ℝ→≤ℚ : ∀ p q → rat p ≤ℝ rat q → p ℚ.≤ q
  ≤ℝ→≤ℚ p q p≤q =
    subst (λ t → p ℚ.≤ t)
      max≡q
      (ℚ.≤max p q)
    where
    p≤q' : maxℝ (rat p) (rat q) ≡ rat q
    p≤q' = p≤q

    ratMax≡ratQ : rat (ℚ.max p q) ≡ rat q
    ratMax≡ratQ = sym (max-rat p q) ∙ p≤q'

    max≡q : ℚ.max p q ≡ q
    max≡q = isInjectiveRat (ℚ.max p q) q ratMax≡ratQ

  ≤ratEquiv : ∀ p q → (rat p ≤ℝ rat q) ≃ (p ℚ.≤ q)
  ≤ratEquiv p q =
    propBiimpl→Equiv
      {A = rat p ≤ℝ rat q} {B = p ℚ.≤ q}
      (isProp≤ℝ (rat p) (rat q)) (ℚ.isProp≤ p q)
      (≤ℝ→≤ℚ p q) (≤ℚ→≤ℝ p q)

  left≤max : ∀ x y → x ≤ℝ maxℝ x y
  left≤max x y =
    maxAssoc x x y
    ∙ cong (λ u → maxℝ u y) (maxIdem x)

  right≤max : ∀ x y → y ≤ℝ maxℝ x y
  right≤max x y =
    subst (y ≤ℝ_) (maxComm y x) (left≤max y x)

  max≤ : ∀ x y z → x ≤ℝ z → y ≤ℝ z → maxℝ x y ≤ℝ z
  max≤ x y z x≤z y≤z =
    sym (maxAssoc x y z)
    ∙ cong (maxℝ x) y≤z
    ∙ x≤z

  maxOf≤ : ∀ x y → x ≤ℝ y → maxℝ x y ≡ y
  maxOf≤ _ _ p = p

  maxPath→≤ℝ : ∀ x y → maxℝ x y ≡ y → x ≤ℝ y
  maxPath→≤ℝ _ _ p = p

isPosetℝ : IsPoset _≤ℝ_
isPosetℝ .IsPoset.is-set = isSetℝ
isPosetℝ .IsPoset.is-prop-valued = isProp≤ℝ
isPosetℝ .IsPoset.is-refl = ≤ℝ-refl
isPosetℝ .IsPoset.is-trans = ≤ℝ-trans
isPosetℝ .IsPoset.is-antisym = ≤ℝ-antisym

ℝ≤Poset : Poset ℓ-zero ℓ-zero
ℝ≤Poset = poset ℝ _≤ℝ_ isPosetℝ
