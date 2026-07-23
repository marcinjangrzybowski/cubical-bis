module Cubical.HITs.CauchyReals.Complex.Conjugation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

import Cubical.Algebra.CommRing as CR

open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra

open import Cubical.Tactics.CommRingSolver.Specialised.Reals


conj : ℂ → ℂ
conj (a , b) = a , -ᵣ b


re-conj : ∀ z → re (conj z) ≡ re z
re-conj _ = refl


im-conj : ∀ z → im (conj z) ≡ -ᵣ im z
im-conj _ = refl


conj-invol : ∀ z → conj (conj z) ≡ z
conj-invol _ = ℂ≡ refl ℝ!


conj-injective : ∀ {z w} → conj z ≡ conj w → z ≡ w
conj-injective {z} {w} p = sym (conj-invol z) ∙ cong conj p ∙ conj-invol w


conj-pres0 : conj 0ℂ ≡ 0ℂ
conj-pres0 = ℂ≡ refl ℝ!


conj-pres1 : conj 1ℂ ≡ 1ℂ
conj-pres1 = ℂ≡ refl ℝ!


conj-pres+ : ∀ z w → conj (z +ℂ w) ≡ conj z +ℂ conj w
conj-pres+ _ _ = ℂ≡ refl ℝ!


conj-pres- : ∀ z → conj (-ℂ z) ≡ -ℂ conj z
conj-pres- _ = ℂ≡ refl ℝ!


conj-pres· : ∀ z w → conj (z ·ℂ w) ≡ conj z ·ℂ conj w
conj-pres· _ _ = ℂ≡ ℝ! ℝ!


conjHom : CR.CommRingHom ℂcommRing ℂcommRing
conjHom .fst = conj
conjHom .snd = CR.makeIsCommRingHom conj-pres1 conj-pres+ conj-pres·


conjIso : Iso ℂ ℂ
conjIso .Iso.fun = conj
conjIso .Iso.inv = conj
conjIso .Iso.sec = conj-invol
conjIso .Iso.ret = conj-invol


conjEquiv : ℂ ≃ ℂ
conjEquiv = isoToEquiv conjIso


conjCommRingEquiv : CR.CommRingEquiv ℂcommRing ℂcommRing
conjCommRingEquiv .fst = conjEquiv
conjCommRingEquiv .snd = conjHom .snd

