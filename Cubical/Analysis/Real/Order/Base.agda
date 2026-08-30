module Cubical.Analysis.Real.Order.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Order as ℚ

open import Cubical.Relation.Binary.Order.Poset

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Lattice


infix 4 _≤ℝ_

_≤ℝ_ : ℝ → ℝ → Type₀
x ≤ℝ y = maxℝ x y ≡ y

isProp≤ℝ : ∀ x y → isProp (x ≤ℝ y)
isProp≤ℝ x y = isSetℝ (maxℝ x y) y

≤ℝ-refl : ∀ x → x ≤ℝ x
≤ℝ-refl = maxIdem

≤ℝ-trans : ∀ x y z → x ≤ℝ y → y ≤ℝ z → x ≤ℝ z
≤ℝ-trans x y z x≤y y≤z =
  cong (maxℝ x) (sym y≤z)
  ∙ maxAssoc x y z
  ∙ cong (λ u → maxℝ u z) x≤y
  ∙ y≤z

≤ℝ-antisym : ∀ x y → x ≤ℝ y → y ≤ℝ x → x ≡ y
≤ℝ-antisym x y x≤y y≤x =
  sym y≤x
  ∙ maxComm y x
  ∙ x≤y

ℝPoset : Poset ℓ-zero ℓ-zero
ℝPoset = poset ℝ _≤ℝ_
  (isposet isSetℝ isProp≤ℝ ≤ℝ-refl ≤ℝ-trans ≤ℝ-antisym)


rat≤rat≃ : ∀ p q →
  (rat p ≤ℝ rat q) ≃ (p ℚ.≤ q)
rat≤rat≃ p q = propBiimpl→Equiv
  (isProp≤ℝ (rat p) (rat q)) (ℚ.isProp≤ _ _)
  toRational fromRational
  where
  toRational : rat p ≤ℝ rat q → p ℚ.≤ q
  toRational real≤ = subst (p ℚ.≤_)
    (rat-injective (sym (max-rat p q) ∙ real≤))
    (ℚ.≤max p q)

  fromRational : p ℚ.≤ q → rat p ≤ℝ rat q
  fromRational p≤q =
    max-rat p q ∙ cong rat (ℚ.≤→max p q p≤q)


left≤max : ∀ x y → x ≤ℝ maxℝ x y
left≤max x y =
  maxAssoc x x y
  ∙ cong (λ u → maxℝ u y) (maxIdem x)

right≤max : ∀ x y → y ≤ℝ maxℝ x y
right≤max x y =
  cong (maxℝ y) (maxComm x y)
  ∙ maxAssoc y y x
  ∙ cong (λ u → maxℝ u x) (maxIdem y)
  ∙ maxComm y x

maxLeastUpperBound : ∀ x y z →
  x ≤ℝ z → y ≤ℝ z → maxℝ x y ≤ℝ z
maxLeastUpperBound x y z x≤z y≤z =
  sym (maxAssoc x y z)
  ∙ cong (maxℝ x) y≤z
  ∙ x≤z

min≤left : ∀ x y → minℝ x y ≤ℝ x
min≤left x y =
  maxComm (minℝ x y) x
  ∙ maxAbsorbMin x y

min≤right : ∀ x y → minℝ x y ≤ℝ y
min≤right x y =
  cong (λ u → maxℝ u y) (minComm x y)
  ∙ maxComm (minℝ y x) y
  ∙ maxAbsorbMin y x
