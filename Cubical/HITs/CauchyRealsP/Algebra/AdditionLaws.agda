module Cubical.HITs.CauchyRealsP.Algebra.AdditionLaws where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra.Extensionality
open import Cubical.HITs.CauchyRealsP.Algebra.Addition

open import Cubical.Relation.Premetric.Mappings

private
  identityIsNonExpanding :
    IsNonExpanding (snd ℝPremetricSpace) (idfun ℝ)
      (snd ℝPremetricSpace)
  identityIsNonExpanding .IsNonExpanding.pres≈ _ _ _ x∼y = x∼y

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

addComm : ∀ x y → x + y ≡ y + x
addComm =
  nonExpandingExtensionality₂
    _+_ (flip _+_)
    addIsNonExpanding₁
    addIsNonExpanding₂
    (λ y → addIsNonExpanding₂ y)
    (λ x → addIsNonExpanding₁ x)
    λ p q →
      rat+rat p q
      ∙ cong rat (ℚ.+Comm p q)
      ∙ sym (rat+rat q p)

addIdR : ∀ x → x + 0 ≡ x
addIdR =
  funExt⁻
    (nonExpandingExtensionality ℝPremetricSpace
      (_+ 0) (idfun ℝ)
      (addIsNonExpanding₁ 0)
      identityIsNonExpanding
      λ q → rat+rat q 0 ∙ cong rat (ℚ.+IdR q))

addIdL : ∀ x → 0 + x ≡ x
addIdL x = addComm 0 x ∙ addIdR x

addAssoc : ∀ x y z → x + (y + z) ≡ (x + y) + z
addAssoc =
  nonExpandingExtensionality₃
    (λ x y z → x + (y + z))
    (λ x y z → (x + y) + z)
    (λ y z → addIsNonExpanding₁ (y + z))
    (λ x z →
      composeIsNonExpanding
        (x +_) (_+ z)
        (addIsNonExpanding₂ x) (addIsNonExpanding₁ z))
    (λ x y →
      composeIsNonExpanding
        (x +_) (y +_)
        (addIsNonExpanding₂ x) (addIsNonExpanding₂ y))
    (λ y z →
      composeIsNonExpanding
        (_+ z) (_+ y)
        (addIsNonExpanding₁ z) (addIsNonExpanding₁ y))
    (λ x z →
      composeIsNonExpanding
        (_+ z) (x +_)
        (addIsNonExpanding₁ z) (addIsNonExpanding₂ x))
    (λ x y → addIsNonExpanding₂ (x + y))
    λ p q r →
      cong (rat p +_) (rat+rat q r)
      ∙ rat+rat p (q ℚ.+ r)
      ∙ cong rat (ℚ.+Assoc p q r)
      ∙ sym (rat+rat (p ℚ.+ q) r)
      ∙ cong (_+ rat r) (sym (rat+rat p q))
