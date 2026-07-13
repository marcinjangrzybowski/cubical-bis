module Cubical.HITs.CauchyReals.InverseLipschitz where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Powerset

open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.InverseLipschitz.Base
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Inverse using
  (invℝ₊-rat; z<x/y₊≃y₊·z<x)
open import Cubical.HITs.CauchyReals.RationalsImports

open ℚ using (_⁻¹₊)

LowerLipschitz-ℝ→ℝℙ :
  ℚ₊ → (P : ℙ ℝ) → (∀ x → x ∈ P → ℝ) → Type
LowerLipschitz-ℝ→ℝℙ m P f =
  ∀ u u∈ v v∈ →
    rat (fst m) ·ᵣ absᵣ (u -ᵣ v) ≤ᵣ
      absᵣ (f u u∈ -ᵣ f v v∈)

opaque
  lowerLipschitz→inverseLipschitz :
    ∀ m P f →
    LowerLipschitz-ℝ→ℝℙ m P f →
    InverseLipschitz-ℝ→ℝℙ (m ⁻¹₊) P f
  lowerLipschitz→inverseLipschitz m P f lower u u∈ v v∈ ε f-close =
    invEq (∼≃abs<ε _ _ _)
     (
      subst (absᵣ (u -ᵣ v) <ᵣ_)
        (cong (rat (fst ε) ·ᵣ_)
           (invℝ₊-rat m)
         ∙ sym (rat·ᵣrat _ _)
         ∙ cong rat (ℚ.·Comm (fst ε) (fst (m ⁻¹₊))))
        (invEq
          (z<x/y₊≃y₊·z<x
            (rat (fst ε))
            (absᵣ (u -ᵣ v))
            (ℚ₊→ℝ₊ m))
          (isTrans≤<ᵣ _ _ _
            (lower u u∈ v v∈)
            (fst (∼≃abs<ε _ _ _) f-close)))
     )
