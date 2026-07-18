{-# OPTIONS --safe #-}

module Cubical.Relation.Binary.Order.Quoset.Mappings where

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma

open import Cubical.Reflection.RecordEquiv

open import Cubical.Relation.Binary.Order.Quoset.Base
open import Cubical.Relation.Binary.Order.Quoset.Subset

private
  variable
    ℓ₀ ℓ₀' ℓ₁ ℓ₁' ℓ₂ ℓ₂' : Level


record IsStrictlyIsotone {A : Type ℓ₀} {B : Type ℓ₁}
  (M : QuosetStr ℓ₀' A) (f : A → B) (N : QuosetStr ℓ₁' B)
  : Type (ℓ-max (ℓ-max ℓ₀ ℓ₀') ℓ₁')
  where
  constructor isstrictlyisotone

  private
    module M = QuosetStr M
    module N = QuosetStr N

  field
    pres< : (x y : A) → x M.< y → f x N.< f y

unquoteDecl IsStrictlyIsotoneIsoΣ =
  declareRecordIsoΣ IsStrictlyIsotoneIsoΣ (quote IsStrictlyIsotone)


isPropIsStrictlyIsotone : {A : Type ℓ₀} {B : Type ℓ₁}
  (M : QuosetStr ℓ₀' A) (f : A → B) (N : QuosetStr ℓ₁' B)
  → isProp (IsStrictlyIsotone M f N)
isPropIsStrictlyIsotone M f N =
  isOfHLevelRetractFromIso 1 IsStrictlyIsotoneIsoΣ
    (isPropΠ3 λ x y _ →
      IsQuoset.is-prop-valued (QuosetStr.isQuoset N) (f x) (f y))


IsStrictlyIsotone-∘ : {A : Type ℓ₀} {B : Type ℓ₁} {C : Type ℓ₂}
  → (M : QuosetStr ℓ₀' A) (f : A → B)
  → (N : QuosetStr ℓ₁' B) (g : B → C) (O : QuosetStr ℓ₂' C)
  → IsStrictlyIsotone M f N
  → IsStrictlyIsotone N g O
  → IsStrictlyIsotone M (g ∘ f) O
IsStrictlyIsotone.pres< (IsStrictlyIsotone-∘ M f N g O isf isg) x y x<y =
  IsStrictlyIsotone.pres< isg (f x) (f y)
    (IsStrictlyIsotone.pres< isf x y x<y)


module _
  {A : Type ℓ₀} {B : Type ℓ₁}
  (M : QuosetStr ℓ₀' A)
  (S : A → hProp ℓ₂)
  (f : ∀ x → ⟨ S x ⟩ → B)
  (N : QuosetStr ℓ₁' B)
  where

  private
    module M = QuosetStr M
    module N = QuosetStr N

  IsStrictlyIsotoneOn : Type _
  IsStrictlyIsotoneOn =
    ∀ x (x∈ : ⟨ S x ⟩) y (y∈ : ⟨ S y ⟩) →
      x M.< y → f x x∈ N.< f y y∈

  isPropIsStrictlyIsotoneOn : isProp IsStrictlyIsotoneOn
  isPropIsStrictlyIsotoneOn = isPropΠ5 λ x x∈ y y∈ _ →
    N.is-prop-valued (f x x∈) (f y y∈)

  IsStrictlyIsotoneOn→IsStrictlyIsotone : IsStrictlyIsotoneOn
    → IsStrictlyIsotone
        ((PredicateQuoset (A , M) S) .snd) (uncurry f) N
  IsStrictlyIsotone.pres<
    (IsStrictlyIsotoneOn→IsStrictlyIsotone is)
    (x , x∈) (y , y∈) x<y =
      is x x∈ y y∈ x<y

  IsStrictlyIsotone→IsStrictlyIsotoneOn :
    IsStrictlyIsotone
      ((PredicateQuoset (A , M) S) .snd) (uncurry f) N
    → IsStrictlyIsotoneOn
  IsStrictlyIsotone→IsStrictlyIsotoneOn is x x∈ y y∈ x<y =
    IsStrictlyIsotone.pres< is (x , x∈) (y , y∈) x<y

  IsStrictlyIsotoneOn≃IsStrictlyIsotone : IsStrictlyIsotoneOn
    ≃ IsStrictlyIsotone
        ((PredicateQuoset (A , M) S) .snd) (uncurry f) N
  IsStrictlyIsotoneOn≃IsStrictlyIsotone =
    propBiimpl→Equiv isPropIsStrictlyIsotoneOn
      (isPropIsStrictlyIsotone
        ((PredicateQuoset (A , M) S) .snd) (uncurry f) N)
      IsStrictlyIsotoneOn→IsStrictlyIsotone
      IsStrictlyIsotone→IsStrictlyIsotoneOn
