module Cubical.HITs.CauchyReals.Analysis.Continuity.Uniform.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset

open import Cubical.Data.Sigma

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals


IsUContinuous : (ℝ → ℝ) → Type
IsUContinuous f =
  ∀ (ε : ℚ₊) → Σ[ δ ∈ ℚ₊ ]
    (∀ u v → u ∼[ δ ] v → f u ∼[ ε ] f v)


IsUContinuousℙ : (P : ℙ ℝ) → (∀ x → x ∈ P → ℝ) → Type
IsUContinuousℙ P f =
  ∀ (ε : ℚ₊) → Σ[ δ ∈ ℚ₊ ]
    (∀ u v u∈ v∈ → u ∼[ δ ] v → f u u∈ ∼[ ε ] f v v∈)


-- Previous location: Continuity.Base.
IsUContinuousℚℙ : (P : ℙ ℝ) → (∀ q → rat q ∈ P → ℝ) → Type
IsUContinuousℚℙ P f =
  ∀ (ε : ℚ₊) → Σ[ δ ∈ ℚ₊ ]
    (∀ u v u∈ v∈ → abs (u ℚ.- v) ℚ.< fst δ →
      f u u∈ ∼[ ε ] f v v∈)


restrIsUContinuousℙ : ∀ P f →
  IsUContinuous f → IsUContinuousℙ P (λ x _ → f x)
restrIsUContinuousℙ _ _ =
  map-snd (((const ∘ const) ∘_) ∘_) ∘_
