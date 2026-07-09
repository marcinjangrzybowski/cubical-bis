module Cubical.HITs.CauchyReals.OrderBounds where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.RationalsImports

∃ℚ₊LargerThanℝ₊ : ∀ (x : ℝ₊) → ∃[ q ∈ ℚ₊ ] fst x <ᵣ rat (fst q)
∃ℚ₊LargerThanℝ₊ x = PT.map
  (λ (q , x<q , _) →
     (q ,  (<ᵣ→<ℚ 0 q (isTrans<ᵣ _ _ _ (snd x) x<q))) , x<q)
   (denseℚinℝ (fst x) (fst x +ᵣ 1)
     (isTrans≡<ᵣ _ _ _
        (sym (+IdR (fst x)))
        (<ᵣ-o+ _ _ (fst x) (decℚ<ᵣ? {0} {1}))))

∃ℚ₊LargerThanℝ₀₊ : ∀ (x : ℝ₀₊) → ∃[ q ∈ ℚ₊ ] fst x <ᵣ rat (fst q)
∃ℚ₊LargerThanℝ₀₊ x = PT.map
  (λ (q , x<q , _) →
     (q ,  (<ᵣ→<ℚ 0 q (isTrans≤<ᵣ _ _ _ (snd x) x<q))) , x<q)
   (denseℚinℝ (fst x) (fst x +ᵣ 1)
     (isTrans≡<ᵣ _ _ _
        (sym (+IdR (fst x)))
        (<ᵣ-o+ _ _ (fst x) (decℚ<ᵣ? {0} {1}))))
