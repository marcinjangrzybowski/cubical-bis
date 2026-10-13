module Cubical.Analysis.Complex.Polynomial.FiniteSumAlgebra where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData as Fin using (Fin; zero; suc)
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.BigOps

module FiniteSums {ℓ} (R : CommRing ℓ) where
  open CommRingStr (snd R)
  open Sum (CommRing→Ring R) public using () renaming (∑ to sumTerms)

  sumExcept : ∀ {n} → (Fin n → fst R) → Fin n → fst R
  sumExcept {suc n} values zero = sumTerms (λ i → values (suc i))
  sumExcept {suc n} values (suc k) = values zero + sumExcept (λ i → values (suc i)) k

  sumSplitSelected : ∀ {n} (values : Fin n → fst R) k →
    sumTerms values ≡ values k + sumExcept values k
  sumSplitSelected {suc n} values zero = refl
  sumSplitSelected {suc n} values (suc k) =
    cong (values zero +_) (sumSplitSelected (λ i → values (suc i)) k)
    ∙ +Assoc (values zero) (values (suc k)) (sumExcept (λ i → values (suc i)) k)
    ∙ cong (_+ sumExcept (λ i → values (suc i)) k) (+Comm (values zero) (values (suc k)))
    ∙ sym (+Assoc (values (suc k)) (values zero) (sumExcept (λ i → values (suc i)) k))
