module Cubical.HITs.CauchyReals.Complex.Algebra where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma

import Cubical.Algebra.CommRing as CR
import Cubical.Algebra.Ring as Ring

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Ring
open import Cubical.HITs.CauchyReals.Complex.Base

open import Cubical.Tactics.CommRingSolver.Specialised.Reals


infixl 6 _+ℂ_ _-ℂ_
infixl 7 _·ℂ_
infix  8 -ℂ_


0ℂ 1ℂ iℂ : ℂ
0ℂ = 0 , 0
1ℂ = 1 , 0
iℂ = 0 , 1


fromℝ : ℝ → ℂ
fromℝ x = x , 0


imagℂ : ℝ → ℂ
imagℂ y = 0 , y


fromℚ : ℚ → ℂ
fromℚ q = fromℝ (rat q)


_+ℂ_ : ℂ → ℂ → ℂ
(a , b) +ℂ (c , d) = (a +ᵣ c) , (b +ᵣ d)


-ℂ_ : ℂ → ℂ
-ℂ (a , b) = (-ᵣ a) , (-ᵣ b)


_-ℂ_ : ℂ → ℂ → ℂ
z -ℂ w = z +ℂ (-ℂ w)


_·ℂ_ : ℂ → ℂ → ℂ
(a , b) ·ℂ (c , d) =
  (a ·ᵣ c -ᵣ b ·ᵣ d) , (a ·ᵣ d +ᵣ b ·ᵣ c)


+ℂAssoc : ∀ z w u → z +ℂ (w +ℂ u) ≡ (z +ℂ w) +ℂ u
+ℂAssoc _ _ _ = ℂ≡ ℝ! ℝ!


+ℂIdR : ∀ z → z +ℂ 0ℂ ≡ z
+ℂIdR _ = ℂ≡ ℝ! ℝ!


+ℂInvR : ∀ z → z +ℂ (-ℂ z) ≡ 0ℂ
+ℂInvR _ = ℂ≡ ℝ! ℝ!


+ℂComm : ∀ z w → z +ℂ w ≡ w +ℂ z
+ℂComm _ _ = ℂ≡ ℝ! ℝ!


·ℂAssoc : ∀ z w u → z ·ℂ (w ·ℂ u) ≡ (z ·ℂ w) ·ℂ u
·ℂAssoc _ _ _ = ℂ≡ ℝ! ℝ!


·ℂIdR : ∀ z → z ·ℂ 1ℂ ≡ z
·ℂIdR _ = ℂ≡ ℝ! ℝ!


·ℂDistR+ : ∀ z w u → z ·ℂ (w +ℂ u) ≡ (z ·ℂ w) +ℂ (z ·ℂ u)
·ℂDistR+ _ _ _ = ℂ≡ ℝ! ℝ!


·ℂComm : ∀ z w → z ·ℂ w ≡ w ·ℂ z
·ℂComm _ _ = ℂ≡ ℝ! ℝ!


IsCommRingℂ : CR.IsCommRing 0ℂ 1ℂ _+ℂ_ _·ℂ_ (-ℂ_)
IsCommRingℂ = CR.makeIsCommRing
  isSetℂ
  +ℂAssoc +ℂIdR +ℂInvR +ℂComm
  ·ℂAssoc ·ℂIdR ·ℂDistR+ ·ℂComm


ℂcommRing : CR.CommRing ℓ-zero
ℂcommRing = ℂ , CR.commringstr 0ℂ 1ℂ _+ℂ_ _·ℂ_ (-ℂ_) IsCommRingℂ


module Cℂ where
  ℂRing = CR.CommRing→Ring ℂcommRing
  open CR.CommRingStr (snd ℂcommRing) public
  open Ring.RingTheory ℂRing public
  open CR.CommRingTheory ℂcommRing public


module Exponentiationℂ = CR.Exponentiation ℂcommRing

open Exponentiationℂ renaming (_^_ to _^ℂ_) public


i²≡-1 : iℂ ·ℂ iℂ ≡ -ℂ 1ℂ
i²≡-1 = ℂ≡ ℝ! ℝ!


fromℝ-pres+ : ∀ x y → fromℝ (x +ᵣ y) ≡ fromℝ x +ℂ fromℝ y
fromℝ-pres+ _ _ = ℂ≡ refl ℝ!


fromℝ-pres· : ∀ x y → fromℝ (x ·ᵣ y) ≡ fromℝ x ·ℂ fromℝ y
fromℝ-pres· _ _ = ℂ≡ ℝ! ℝ!


ℝ→ℂHom : CR.CommRingHom ℝcommRing ℂcommRing
ℝ→ℂHom .fst = fromℝ
ℝ→ℂHom .snd = CR.makeIsCommRingHom refl fromℝ-pres+ fromℝ-pres·


fromℚ-pres+ : ∀ x y → fromℚ (x ℚ.+ y) ≡ fromℚ x +ℂ fromℚ y
fromℚ-pres+ x y = ℂ≡ (sym (+ᵣ-rat x y)) ℝ!


fromℚ-pres· : ∀ x y → fromℚ (x ℚ.· y) ≡ fromℚ x ·ℂ fromℚ y
fromℚ-pres· x y = ℂ≡ (rat·ᵣrat x y ∙ ℝ!) ℝ!
