module Cubical.HITs.CauchyReals.Complex.Transcendental.Exponential where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sum

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Exponentiation.RealPower.Definition using
  (^ᵣ0; ^ᵣ+)
open import Cubical.HITs.CauchyReals.Exponentiation.Normalized.Exponential
open import Cubical.HITs.CauchyReals.Trigonometry.Base using
  (sin; cos; sin0=0; cos0=1; sin-odd; cos-even
  ; sin·sin+cos·cos=1)
open import Cubical.HITs.CauchyReals.Trigonometry.Pi using
  (sinOfSum; cosOfSum)

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Conjugation
open import Cubical.HITs.CauchyReals.Complex.NormSquared
open import Cubical.HITs.CauchyReals.Complex.Apartness
open import Cubical.HITs.CauchyReals.Complex.Modulus.Definition
open import Cubical.HITs.CauchyReals.Complex.Modulus.Laws
open import Cubical.HITs.CauchyReals.Complex.Modulus.Positive
open import Cubical.HITs.CauchyReals.Complex.Polar using
  (scaleℂ; modulus-scale-positive; modulus-scale-unit)
open import Cubical.HITs.CauchyReals.Complex.UnitCircle
open import Cubical.HITs.CauchyReals.Complex.Transcendental.Cis public

open import Cubical.Tactics.CommRingSolver.Specialised.Reals


scale-mul : ∀ r s z w →
  scaleℂ (r ·ᵣ s) (z ·ℂ w) ≡ scaleℂ r z ·ℂ scaleℂ s w
scale-mul _ _ _ _ = ℂ≡ ℝ! ℝ!


conj-scale : ∀ r z → conj (scaleℂ r z) ≡ scaleℂ r (conj z)
conj-scale _ _ = ℂ≡ ℝ! ℝ!


realExp-add : ∀ x y →
  fst (realExp (x +ᵣ y)) ≡ fst (realExp x) ·ᵣ fst (realExp y)
realExp-add x y = cong fst (^ᵣ+ eBase x y)


realExp0 : fst (realExp 0) ≡ 1
realExp0 = ^ᵣ0 eBase


expℂ : ℂ → ℂ
expℂ z = scaleℂ (fst (realExp (re z))) (cis (im z))


expℂ0 : expℂ 0ℂ ≡ 1ℂ
expℂ0 = cong₂ scaleℂ realExp0 cis0 ∙ Cℂ.·IdL 1ℂ


expℂ-add : ∀ z w → expℂ (z +ℂ w) ≡ expℂ z ·ℂ expℂ w
expℂ-add (a , b) (c , d) =
  cong₂ scaleℂ (realExp-add a c) (cis-add b d)
  ∙ scale-mul (fst (realExp a)) (fst (realExp c)) (cis b) (cis d)


expℂ-conj : ∀ z → expℂ (conj z) ≡ conj (expℂ z)
expℂ-conj (a , b) =
  cong (scaleℂ (fst (realExp a))) (cis-neg b)
  ∙ sym (conj-scale (fst (realExp a)) (cis b))


opaque
  expℂ-scale-unit-path : ∀ z →
    expℂ z ≡
      scaleℂ (fst (realExp (re z))) (fst (cisUnit (im z)))
  expℂ-scale-unit-path z = refl


opaque
  modulus-scaled-unit-along-path : ∀ w (r : ℝ₊) (u : UnitCircleℂ) →
    w ≡ scaleℂ (fst r) (fst u) → modulus w ≡ fst r
  modulus-scaled-unit-along-path w r u w≡ru =
    cong modulus w≡ru ∙ modulus-scale-unit r u


opaque
  modulus-expℂ : ∀ z → modulus (expℂ z) ≡ fst (realExp (re z))
  modulus-expℂ z = modulus-scaled-unit-along-path
    (expℂ z) (realExp (re z)) (cisUnit (im z))
    (expℂ-scale-unit-path z)


opaque
  positive-left-of-path : ∀ x y → x ≡ y → 0 <ᵣ y → 0 <ᵣ x
  positive-left-of-path x y x≡y = subst (0 <ᵣ_) (sym x≡y)


opaque
  modulus-expℂ-positive : ∀ z → 0 <ᵣ modulus (expℂ z)
  modulus-expℂ-positive z = positive-left-of-path
    (modulus (expℂ z)) (fst (realExp (re z)))
    (modulus-expℂ z) (snd (realExp (re z)))


opaque
  expApart-from-positive-modulus : ∀ z → 0 <ᵣ modulus z → 0ℂ #ℂ z
  expApart-from-positive-modulus z = 0<modulus→0#ℂ


opaque
  0#expℂ : ∀ z → 0ℂ #ℂ expℂ z
  0#expℂ z = expApart-from-positive-modulus
    (expℂ z) (modulus-expℂ-positive z)


expℂ-neg-inverse : ∀ z → expℂ z ·ℂ expℂ (-ℂ z) ≡ 1ℂ
expℂ-neg-inverse z =
  sym (expℂ-add z (-ℂ z))
  ∙ cong expℂ (+ℂInvR z)
  ∙ expℂ0


expℂ-real : ∀ x → expℂ (fromℝ x) ≡ fromℝ (fst (realExp x))
expℂ-real x = cong (scaleℂ (fst (realExp x))) cis0
  ∙ ·ℂIdR (fromℝ (fst (realExp x)))


euler-complex : ∀ x → expℂ (imagℂ x) ≡ cis x
euler-complex x = cong₂ scaleℂ realExp0 refl ∙ Cℂ.·IdL (cis x)


euler-formula : ∀ x → expℂ (imagℂ x) ≡
  fromℝ (cos x) +ℂ iℂ ·ℂ fromℝ (sin x)
euler-formula x = euler-complex x ∙ ℂ≡ ℝ! ℝ!
