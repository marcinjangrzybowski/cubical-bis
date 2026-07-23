module Cubical.HITs.CauchyReals.Complex.Apartness where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Powerset

open import Cubical.Data.Empty
open import Cubical.Relation.Nullary

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Order.Properties using
  (isIrrefl<ᵣ)
open import Cubical.HITs.CauchyReals.Algebra.Order.Positive using
  (positiveMulClosed)

open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Conjugation
open import Cubical.HITs.CauchyReals.Complex.NormSquared

open import Cubical.Tactics.CommRingSolver.Specialised.Reals


infix 4 _#ℂ_


_#ℂ_ : ℂ → ℂ → Type
z #ℂ w = 0 <ᵣ normSq (z -ℂ w)


isProp#ℂ : ∀ z w → isProp (z #ℂ w)
isProp#ℂ z w = isProp<ᵣ _ _


0#ℂₚ : ℂ → hProp ℓ-zero
0#ℂₚ z = (0ℂ #ℂ z) , isProp#ℂ _ _


normSq-self-difference : ∀ z → normSq (z -ℂ z) ≡ 0
normSq-self-difference _ = ℝ!


normSq-difference-sym : ∀ z w →
  normSq (z -ℂ w) ≡ normSq (w -ℂ z)
normSq-difference-sym _ _ = ℝ!


normSq-zero-difference : ∀ z → normSq (0ℂ -ℂ z) ≡ normSq z
normSq-zero-difference _ = ℝ!


normSq-difference-zero : ∀ z → normSq (z -ℂ 0ℂ) ≡ normSq z
normSq-difference-zero _ = ℝ!


normSq-translate-difference : ∀ z w u →
  normSq ((z +ℂ u) -ℂ (w +ℂ u)) ≡ normSq (z -ℂ w)
normSq-translate-difference _ _ _ = ℝ!


normSq-neg-difference : ∀ z w →
  normSq ((-ℂ z) -ℂ (-ℂ w)) ≡ normSq (z -ℂ w)
normSq-neg-difference _ _ = ℝ!


normSq-conj-difference : ∀ z w →
  normSq (conj z -ℂ conj w) ≡ normSq (z -ℂ w)
normSq-conj-difference _ _ = ℝ!


#ℂ-sym : ∀ {z w} → z #ℂ w → w #ℂ z
#ℂ-sym {z} {w} z#w =
  subst (0 <ᵣ_) (normSq-difference-sym z w) z#w


#ℂ→≢ : ∀ {z w} → z #ℂ w → ¬ z ≡ w
#ℂ→≢ {z} {w} z#w z≡w =
  let z#z = subst (z #ℂ_) (sym z≡w) z#w
  in isIrrefl<ᵣ 0 (subst (0 <ᵣ_) (normSq-self-difference z) z#z)


#ℂ-translate-right : ∀ {z w} u → z #ℂ w →
  (z +ℂ u) #ℂ (w +ℂ u)
#ℂ-translate-right {z} {w} u z#w =
  subst (0 <ᵣ_) (sym (normSq-translate-difference z w u)) z#w


#ℂ-translate-right⁻ : ∀ {z w} u →
  (z +ℂ u) #ℂ (w +ℂ u) → z #ℂ w
#ℂ-translate-right⁻ {z} {w} u p =
  subst (0 <ᵣ_) (normSq-translate-difference z w u) p


#ℂ-translate-right≃ : ∀ z w u →
  (z #ℂ w) ≃ ((z +ℂ u) #ℂ (w +ℂ u))
#ℂ-translate-right≃ z w u =
  propBiimpl→Equiv (isProp#ℂ _ _) (isProp#ℂ _ _)
    (#ℂ-translate-right u) (#ℂ-translate-right⁻ u)


#ℂ-neg : ∀ {z w} → z #ℂ w → (-ℂ z) #ℂ (-ℂ w)
#ℂ-neg {z} {w} z#w =
  subst (0 <ᵣ_) (sym (normSq-neg-difference z w)) z#w


#ℂ-conj : ∀ {z w} → z #ℂ w → conj z #ℂ conj w
#ℂ-conj {z} {w} z#w =
  subst (0 <ᵣ_) (sym (normSq-conj-difference z w)) z#w


0#ℂ→0<normSq : ∀ {z} → 0ℂ #ℂ z → 0 <ᵣ normSq z
0#ℂ→0<normSq {z} 0#z =
  subst (0 <ᵣ_) (normSq-zero-difference z) 0#z


0<normSq→0#ℂ : ∀ {z} → 0 <ᵣ normSq z → 0ℂ #ℂ z
0<normSq→0#ℂ {z} 0<norm =
  subst (0 <ᵣ_) (sym (normSq-zero-difference z)) 0<norm


0#ℂ≃0<normSq : ∀ z → (0ℂ #ℂ z) ≃ (0 <ᵣ normSq z)
0#ℂ≃0<normSq z =
  propBiimpl→Equiv (isProp#ℂ _ _) (isProp<ᵣ _ _)
    0#ℂ→0<normSq 0<normSq→0#ℂ


0#ℂ-mul : ∀ {z w} → 0ℂ #ℂ z → 0ℂ #ℂ w → 0ℂ #ℂ (z ·ℂ w)
0#ℂ-mul {z} {w} 0#z 0#w =
  0<normSq→0#ℂ
    (subst (0 <ᵣ_) (sym (normSq-mul z w))
      (positiveMulClosed (normSq z) (normSq w)
        (0#ℂ→0<normSq 0#z) (0#ℂ→0<normSq 0#w)))
