module Cubical.Relation.Binary.Order.Pseudolattice.Clamp where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Binary.Order.Poset.Interval
open import Cubical.Relation.Binary.Order.Pseudolattice.Base
open import Cubical.Relation.Binary.Order.Pseudolattice.Properties

private
  variable
    ℓ ℓ' : Level


module PseudolatticeClamp (L≤ : Pseudolattice ℓ ℓ') where
  private
    L = L≤ .fst

  open PseudolatticeStr (L≤ .snd)
  open PseudolatticeTheory L≤

  clamp : L → L → L → L
  clamp lower upper x = (lower ∨l x) ∧l upper

  ∧Isotone : ∀ {a b c d} → a ≤ b → c ≤ d → a ∧l c ≤ b ∧l d
  ∧Isotone {a} {b} {c} {d} a≤b c≤d =
    ∧GLB
      (is-trans (a ∧l c) a b ∧≤L a≤b)
      (is-trans (a ∧l c) c d ∧≤R c≤d)

  ∨Isotone : ∀ {a b c d} → a ≤ b → c ≤ d → a ∨l c ≤ b ∨l d
  ∨Isotone {a} {b} {c} {d} a≤b c≤d =
    ∨LUB
      (is-trans a b (b ∨l d) a≤b L≤∨)
      (is-trans c d (b ∨l d) c≤d R≤∨)

  clampIsotone : ∀ lower upper x y → x ≤ y →
    clamp lower upper x ≤ clamp lower upper y
  clampIsotone lower upper x y x≤y =
    ∧Isotone (∨Isotone (is-refl lower) x≤y) (is-refl upper)

  clamp≤Upper : ∀ lower upper x → clamp lower upper x ≤ upper
  clamp≤Upper lower upper x = ∧≤R

  lower≤Clamp : ∀ lower upper x → lower ≤ upper →
    lower ≤ clamp lower upper x
  lower≤Clamp lower upper x lower≤upper =
    ∧GLB L≤∨ lower≤upper

  belowLower→clamp≡Lower : ∀ lower upper x →
    lower ≤ upper → x ≤ lower → clamp lower upper x ≡ lower
  belowLower→clamp≡Lower lower upper x lower≤upper x≤lower =
    cong (_∧l upper) (≥→∨≡Left x≤lower)
    ∙ ≤→∧≡Left lower≤upper

  aboveUpper→clamp≡Upper : ∀ lower upper x →
    lower ≤ upper → upper ≤ x → clamp lower upper x ≡ upper
  aboveUpper→clamp≡Upper lower upper x lower≤upper upper≤x =
    cong (_∧l upper)
      (≤→∨≡Right (is-trans lower upper x lower≤upper upper≤x))
    ∙ ≥→∧≡Right upper≤x

  clampInterval : ∀ lower upper x → lower ≤ upper →
    Interval (Pseudolattice→Poset L≤) lower upper
  clampInterval lower upper x lower≤upper =
    interval
      (clamp lower upper x)
      (lower≤Clamp lower upper x lower≤upper)
      (clamp≤Upper lower upper x)
