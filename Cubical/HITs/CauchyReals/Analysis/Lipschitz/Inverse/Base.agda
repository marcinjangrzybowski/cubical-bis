module Cubical.HITs.CauchyReals.Analysis.Lipschitz.Inverse.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Powerset

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Foundation.Rationals

open ℚ using (_⁻¹₊)

InverseLipschitz-ℝ→ℝℙ :
  ℚ₊ → (P : ℙ ℝ) → (∀ x → x ∈ P → ℝ) → Type
InverseLipschitz-ℝ→ℝℙ K P f =
  ∀ u u∈ v v∈ → (ε : ℚ₊) →
    f u u∈ ∼[ ε ] f v v∈ → u ∼[ K ·₊ ε ] v

opaque
  InverseLipschitz-ℝ→ℝℙ→injective : ∀ K P f →
    InverseLipschitz-ℝ→ℝℙ K P f →
    ∀ x x∈ y y∈ → f x x∈ ≡ f y y∈ → x ≡ y
  InverseLipschitz-ℝ→ℝℙ→injective K P f invLip x x∈ y y∈ fxy =
    fst (∼≃≡ x y) x~y
    where
    f-close : ∀ ε → f x x∈ ∼[ ε ] f y y∈
    f-close = invEq (∼≃≡ (f x x∈) (f y y∈)) fxy

    x~y : ∀ ε → x ∼[ ε ] y
    x~y ε =
      subst∼ (ℚ.y·[x/y] K (fst ε))
        (invLip x x∈ y y∈ (K ⁻¹₊ ·₊ ε) (f-close (K ⁻¹₊ ·₊ ε)))
