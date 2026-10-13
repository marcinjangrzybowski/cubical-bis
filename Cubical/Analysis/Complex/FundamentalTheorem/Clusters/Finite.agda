module Cubical.Analysis.Complex.FundamentalTheorem.Clusters.Finite where

-- Combine only finitely many radius witnesses. This lemma cannot be used
-- to choose a sequence from radiuswise truncated existence statements.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData using (Fin; zero; suc)
open import Cubical.Data.Sigma
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

finite-common-radius : ∀ n (P : Fin n → ℚ₊ → Type₀) →
  (∀ i δ ε → δ ≤₊ ε → P i ε → P i δ) →
  (∀ i → PT.∥ Σ[ ε ∈ ℚ₊ ] P i ε ∥₁) →
  PT.∥ Σ[ ε ∈ ℚ₊ ] (∀ i → P i ε) ∥₁
finite-common-radius zero P shrink witnesses = PT.∣ 1 , (λ ()) ∣₁
finite-common-radius (suc n) P shrink witnesses = PT.map2
  (λ { (δ , head) (ε , tail) → min₊ δ ε , λ
    { zero → shrink zero (min₊ δ ε) δ (min₊≤L δ ε) head
    ; (suc i) → shrink (suc i) (min₊ δ ε) ε (min₊≤R δ ε) (tail i) } })
  (witnesses zero)
  (finite-common-radius n (λ i ε → P (suc i) ε)
    (λ i → shrink (suc i)) (λ i → witnesses (suc i)))

finite-common-radius₂ : ∀ m n (P : Fin m → Fin n → ℚ₊ → Type₀) →
  (∀ i j δ ε → δ ≤₊ ε → P i j ε → P i j δ) →
  (∀ i j → PT.∥ Σ[ ε ∈ ℚ₊ ] P i j ε ∥₁) →
  PT.∥ Σ[ ε ∈ ℚ₊ ] (∀ i j → P i j ε) ∥₁
finite-common-radius₂ m n P shrink witnesses =
  finite-common-radius m (λ i ε → ∀ j → P i j ε)
    (λ i δ ε below all j → shrink i j δ ε below (all j))
    (λ i → finite-common-radius n (P i) (shrink i) (witnesses i))
