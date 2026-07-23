module Cubical.HITs.CauchyReals.Complex.NormSquared where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Power.Base
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition.Base
open import Cubical.HITs.CauchyReals.Complex.Base
open import Cubical.HITs.CauchyReals.Complex.Algebra
open import Cubical.HITs.CauchyReals.Complex.Conjugation

open import Cubical.Tactics.CommRingSolver.Specialised.Reals


normSq : ℂ → ℝ
normSq (a , b) = a ·ᵣ a +ᵣ b ·ᵣ b


squareNonNeg : ∀ x → 0 ≤ᵣ x ·ᵣ x
squareNonNeg x = subst (0 ≤ᵣ_) (x^²=x·x x) (0≤ᵣx² x)


normSqNonNeg : ∀ z → 0 ≤ᵣ normSq z
normSqNonNeg (a , b) =
  isTrans≡≤ᵣ _ _ _
    (sym (+ᵣ-rat 0 0))
    (≤ᵣMonotone+ᵣ _ _ _ _ (squareNonNeg a) (squareNonNeg b))


normSq0 : normSq 0ℂ ≡ 0
normSq0 = ℝ!


normSq1 : normSq 1ℂ ≡ 1
normSq1 = ℝ!


normSqi : normSq iℂ ≡ 1
normSqi = ℝ!


normSq-neg : ∀ z → normSq (-ℂ z) ≡ normSq z
normSq-neg _ = ℝ!


normSq-conj : ∀ z → normSq (conj z) ≡ normSq z
normSq-conj _ = ℝ!


mul-conj : ∀ z → z ·ℂ conj z ≡ fromℝ (normSq z)
mul-conj _ = ℂ≡ ℝ! ℝ!


conj-mul : ∀ z → conj z ·ℂ z ≡ fromℝ (normSq z)
conj-mul z = ·ℂComm _ _ ∙ mul-conj z


normSq-mul : ∀ z w → normSq (z ·ℂ w) ≡ normSq z ·ᵣ normSq w
normSq-mul _ _ = ℝ!


normSq-fromℝ : ∀ x → normSq (fromℝ x) ≡ x ·ᵣ x
normSq-fromℝ _ = ℝ!


normSq-imag : ∀ x → normSq (imagℂ x) ≡ x ·ᵣ x
normSq-imag _ = ℝ!
