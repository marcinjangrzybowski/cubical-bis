module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals.Base as ℚ
import Cubical.Data.Rationals.Order as ℚ

open import Cubical.Relation.Binary.Order.Poset

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Absorption


-- Associative, commutative, idempotent max induces an unconditional partial
-- order.  This is an internal order on the new real type; no reflection claim
-- about the rational embedding is used in its construction.

ℝFormulaPoset : Poset ℓ-zero ℓ-zero
ℝFormulaPoset .fst = Real.ℝ
ℝFormulaPoset .snd .PosetStr._≤_ = _≤ℝ_
ℝFormulaPoset .snd .PosetStr.isPoset .IsPoset.is-set =
  Real.Base.isSetCompletion
ℝFormulaPoset .snd .PosetStr.isPoset .IsPoset.is-prop-valued =
  isProp≤ℝ
ℝFormulaPoset .snd .PosetStr.isPoset .IsPoset.is-refl =
  ≤ℝ-refl
ℝFormulaPoset .snd .PosetStr.isPoset .IsPoset.is-trans =
  ≤ℝ-trans
ℝFormulaPoset .snd .PosetStr.isPoset .IsPoset.is-antisym =
  ≤ℝ-antisym


≤ℚ→≤ℝ : ∀ p q → p ℚ.≤ q → Real.ιℚ p ≤ℝ Real.ιℚ q
≤ℚ→≤ℝ p q p≤q =
    max-ι p q
  ∙ cong Real.ιℚ (ℚ.≤→max p q p≤q)


max-upper-left : ∀ x y → x ≤ℝ (x ⊔ℝ y)
max-upper-left x y =
    max-assoc x x y
  ∙ cong (_⊔ℝ y) (max-idempotent x)

max-upper-right : ∀ x y → y ≤ℝ (x ⊔ℝ y)
max-upper-right x y =
    max-comm y (x ⊔ℝ y)
  ∙ sym (max-assoc x y y)
  ∙ cong (x ⊔ℝ_) (max-idempotent y)

max-least : ∀ x y z →
  x ≤ℝ z → y ≤ℝ z → (x ⊔ℝ y) ≤ℝ z
max-least x y z x≤z y≤z =
    sym (max-assoc x y z)
  ∙ cong (x ⊔ℝ_) y≤z
  ∙ x≤z


min-lower-left : ∀ x y → (x ⊓ℝ y) ≤ℝ x
min-lower-left x y =
    max-comm (x ⊓ℝ y) x
  ∙ max-absorb-min x y

min-lower-right : ∀ x y → (x ⊓ℝ y) ≤ℝ y
min-lower-right x y =
    max-comm (x ⊓ℝ y) y
  ∙ cong (y ⊔ℝ_) (min-comm x y)
  ∙ max-absorb-min y x

≤ℝ→min : ∀ x y → x ≤ℝ y → x ⊓ℝ y ≡ x
≤ℝ→min x y x≤y =
  cong (x ⊓ℝ_) (sym x≤y)
  ∙ min-absorb-max x y

min→≤ℝ : ∀ x y → x ⊓ℝ y ≡ x → x ≤ℝ y
min→≤ℝ x y meet≡x =
  subst (_≤ℝ y) meet≡x (min-lower-right x y)

min-greatest : ∀ x y z →
  z ≤ℝ x → z ≤ℝ y → z ≤ℝ (x ⊓ℝ y)
min-greatest x y z z≤x z≤y =
    max-comm z (x ⊓ℝ y)
  ∙ cong ((x ⊓ℝ y) ⊔ℝ_) (sym meet-is-z)
  ∙ max-absorb-min (x ⊓ℝ y) z
  where
  meet-is-z : (x ⊓ℝ y) ⊓ℝ z ≡ z
  meet-is-z =
      min-comm (x ⊓ℝ y) z
    ∙ min-assoc z x y
    ∙ cong (_⊓ℝ y) (≤ℝ→min z x z≤x)
    ∙ ≤ℝ→min z y z≤y
