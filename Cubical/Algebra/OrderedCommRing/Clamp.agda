module Cubical.Algebra.OrderedCommRing.Clamp where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.Ring
open import Cubical.Algebra.OrderedCommRing.Base
open import Cubical.Algebra.OrderedCommRing.Properties

open import Cubical.Relation.Binary.Order.Pseudolattice.Clamp
open import Cubical.Relation.Binary.Order.Pseudolattice.Properties

open import Cubical.Tactics.CommRingSolver

private
  variable
    ℓ ℓ' : Level


module OrderedCommRingClamp (R≤ : OrderedCommRing ℓ ℓ') where
  private
    RCR = OrderedCommRing→CommRing R≤

  open OrderedCommRingStr (R≤ .snd)
  open OrderedCommRingTheory R≤
  open OrderedCommRingReasoning R≤
  open PseudolatticeTheory (OrderedCommRing→PseudoLattice R≤) renaming (
      L≤∨ to L≤⊔ ; R≤∨ to R≤⊔ ; ∨LUB to ⊔LUB
    ; ∧≤L to ⊓≤L ; ∧≤R to ⊓≤R ; ∧GLB to ⊓GLB)
  open PseudolatticeClamp (OrderedCommRing→PseudoLattice R≤) public

  private
    module R = RingTheory (OrderedCommRing→Ring R≤)
    open R

    +R≤→≤-R : ∀ x y z → x + z ≤ y → x ≤ y - z
    +R≤→≤-R x y z x+z≤y = begin≤
      x               ≡→≤⟨ solve! RCR ⟩
      (x + z) + (- z)   ≤⟨ +MonoR≤ _ _ (- z) x+z≤y ⟩
      y - z             ◾

    ≤-R→+R≤ : ∀ x y z → x ≤ y - z → x + z ≤ y
    ≤-R→+R≤ x y z x≤y-z = begin≤
      x + z             ≤⟨ +MonoR≤ _ _ z x≤y-z ⟩
      (y - z) + z     ≡→≤⟨ solve! RCR ⟩
      y                 ◾

    ≤+R→-R≤ : ∀ x y z → x ≤ y + z → x - z ≤ y
    ≤+R→-R≤ x y z x≤y+z = begin≤
      x - z             ≤⟨ +MonoR≤ _ _ (- z) x≤y+z ⟩
      (y + z) + (- z) ≡→≤⟨ solve! RCR ⟩
      y                 ◾

    ≤-R→≤+R : ∀ x y z → x - z ≤ y → x ≤ y + z
    ≤-R→≤+R x y z x-z≤y = begin≤
      x                 ≡→≤⟨ solve! RCR ⟩
      (x - z) + z         ≤⟨ +MonoR≤ _ _ z x-z≤y ⟩
      y + z               ◾

  +DistR⊔ : ∀ x y z → (x ⊔ y) + z ≡ (x + z) ⊔ (y + z)
  +DistR⊔ x y z = is-antisym _ _
    (≤-R→+R≤ (x ⊔ y) ((x + z) ⊔ (y + z)) z
      (⊔LUB
        (+R≤→≤-R x ((x + z) ⊔ (y + z)) z L≤⊔)
        (+R≤→≤-R y ((x + z) ⊔ (y + z)) z R≤⊔)))
    (⊔LUB
      (+MonoR≤ x (x ⊔ y) z L≤⊔)
      (+MonoR≤ y (x ⊔ y) z R≤⊔))

  +DistR⊓ : ∀ x y z → (x ⊓ y) + z ≡ (x + z) ⊓ (y + z)
  +DistR⊓ x y z = is-antisym _ _
    (⊓GLB
      (+MonoR≤ (x ⊓ y) x z ⊓≤L)
      (+MonoR≤ (x ⊓ y) y z ⊓≤R))
    (≤-R→≤+R ((x + z) ⊓ (y + z)) (x ⊓ y) z
      (⊓GLB
        (≤+R→-R≤ ((x + z) ⊓ (y + z)) x z ⊓≤L)
        (≤+R→-R≤ ((x + z) ⊓ (y + z)) y z ⊓≤R)))

  clampTranslate : ∀ lower upper x z →
    clamp (lower + z) (upper + z) (x + z) ≡
    clamp lower upper x + z
  clampTranslate lower upper x z =
    cong (_⊓ (upper + z)) (sym (+DistR⊔ lower x z))
    ∙ sym (+DistR⊓ (lower ⊔ x) upper z)

  clampDelta : ∀ lower upper x → clamp lower upper x ≡
    x + clamp (lower - x) (upper - x) 0r
  clampDelta lower upper x =
    cong₃ clamp (solve! RCR) (solve! RCR) (solve! RCR)
    ∙ clampTranslate (lower - x) (upper - x) 0r x
    ∙ +Comm _ x

  clampShift≤ : ∀ lower upper x d → 0r ≤ d →
    clamp lower upper (x + d) ≤ clamp lower upper x + d
  clampShift≤ lower upper x d 0≤d = begin≤
    clamp lower upper (x + d)
      ≤⟨ ∧Isotone
        (⊔LUB
          (is-trans≤ lower (lower ⊔ x) ((lower ⊔ x) + d)
            L≤⊔ (≤SumLeftNonNeg (lower ⊔ x) d 0≤d))
          (+MonoR≤ x (lower ⊔ x) d R≤⊔))
        (≤SumLeftNonNeg upper d 0≤d) ⟩
    ((lower ⊔ x) + d) ⊓ (upper + d)
      ≡→≤⟨ sym (+DistR⊓ (lower ⊔ x) upper d) ⟩
    clamp lower upper x + d ◾

  clampDiff : ∀ lower upper x y → x ≤ y →
    clamp lower upper y - clamp lower upper x ≤ y - x
  clampDiff lower upper x y x≤y = begin≤
    clamp lower upper y - clamp lower upper x
      ≤⟨ +MonoR≤ _ _ (- clamp lower upper x)
        (is-trans≤ _ _ _
          (clampIsotone lower upper y (x + (y - x))
            (subst (y ≤_) (solve! RCR) (is-refl y)))
          (clampShift≤ lower upper x (y - x) (≤→0≤Δ x y x≤y))) ⟩
    (clamp lower upper x + (y - x)) - clamp lower upper x
      ≡→≤⟨ solve! RCR ⟩
    y - x ◾

  private
    clampDiff≤abs : ∀ lower upper x y →
      clamp lower upper y - clamp lower upper x ≤ abs (y - x)
    clampDiff≤abs lower upper x y = begin≤
      clamp lower upper y - clamp lower upper x
        ≤⟨ +MonoR≤ _ _ (- clamp lower upper x)
          (is-trans≤ _ _ _
            (clampIsotone lower upper y
              (x + abs (y - x))
              (begin≤
                y                 ≡→≤⟨ solve! RCR ⟩
                x + (y - x)        ≤⟨ +MonoL≤ _ _ x (≤abs (y - x)) ⟩
                x + abs (y - x)    ◾))
            (clampShift≤ lower upper x (abs (y - x)) (0≤abs (y - x)))) ⟩
      (clamp lower upper x + abs (y - x)) - clamp lower upper x
        ≡→≤⟨ solve! RCR ⟩
      abs (y - x) ◾

  clampDist : ∀ lower upper x y →
    abs (clamp lower upper y - clamp lower upper x) ≤ abs (y - x)
  clampDist lower upper x y = ⊔LUB
    (clampDiff≤abs lower upper x y)
    (begin≤
      - (clamp lower upper y - clamp lower upper x)
        ≡→≤⟨ solve! RCR ⟩
      clamp lower upper x - clamp lower upper y
        ≤⟨ clampDiff≤abs lower upper y x ⟩
      abs (x - y)
        ≡→≤⟨ abs-Comm x y ⟩
      abs (y - x) ◾)
