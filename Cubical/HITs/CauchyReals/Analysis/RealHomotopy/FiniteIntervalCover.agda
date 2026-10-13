module Cubical.HITs.CauchyReals.Analysis.RealHomotopy.FiniteIntervalCover where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData.Base as Fin using (Fin; fromℕ)
open import Cubical.Data.Unit using (Unit)
open import Cubical.Data.Sum using (inl; inr)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CauchyReals.Foundation.Base using (ℝ)
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Base using (Dichotomyℝ')

-- Strict positive overlaps suffice. No point is assigned to a closed
-- grid cell and no order decision or rational approximation is needed.
Overlaps : (n : ℕ) → (Fin (suc n) → ℝ) → (Fin (suc n) → ℝ) → Type
Overlaps zero a b = Unit
Overlaps (suc n) a b = (a (Fin.suc Fin.zero) <ᵣ b Fin.zero) ×
  Overlaps n (λ i → a (Fin.suc i)) (λ i → b (Fin.suc i))

openChainCover : (n : ℕ) (a b : Fin (suc n) → ℝ) → Overlaps n a b →
  (x : ℝ) → a Fin.zero <ᵣ x → x <ᵣ b (fromℕ n) →
  ∥ Σ[ i ∈ Fin (suc n) ] (a i <ᵣ x) × (x <ᵣ b i) ∥₁
openChainCover zero a b overlaps x lo hi = ∣ Fin.zero , lo , hi ∣₁
openChainCover (suc n) a b (gap , tail) x lo hi = PT.rec squash₁
  (λ where
    (inl left) → ∣ Fin.zero , lo , left ∣₁
    (inr right) → PT.map (λ (i , lower , upper) → Fin.suc i , lower , upper)
      (openChainCover n (λ i → a (Fin.suc i)) (λ i → b (Fin.suc i)) tail x right hi))
  (Dichotomyℝ' (a (Fin.suc Fin.zero)) x (b Fin.zero) gap)
