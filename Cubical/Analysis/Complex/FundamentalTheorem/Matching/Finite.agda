module Cubical.Analysis.Complex.FundamentalTheorem.Matching.Finite where

-- Explicit finite permutations used when matching and removing one root.
-- This construction manipulates positions only; it never compares roots.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat using (suc)
open import Cubical.Data.FinData using (Fin; zero; suc; snotz; injSucFin; finSucMaybeIso)
open import Cubical.Data.Maybe using (congMaybeEquiv)
open import Cubical.Data.Vec using (Vec; []; _∷_; lookup; drop)
import Cubical.Data.Empty as ⊥

-- Fin (suc n) is Maybe (Fin n); lift through the existing equivalences.
liftPermutation : ∀ {n} → Fin n ≃ Fin n → Fin (suc n) ≃ Fin (suc n)
liftPermutation σ = compEquiv (isoToEquiv finSucMaybeIso)
  (compEquiv (congMaybeEquiv σ) (isoToEquiv (invIso finSucMaybeIso)))

private
  swapFirst : ∀ {n} → Fin (suc (suc n)) → Fin (suc (suc n))
  swapFirst zero = suc zero
  swapFirst (suc zero) = zero
  swapFirst (suc (suc i)) = suc (suc i)

  swapFirst² : ∀ {n} (i : Fin (suc (suc n))) → swapFirst (swapFirst i) ≡ i
  swapFirst² zero = refl
  swapFirst² (suc zero) = refl
  swapFirst² (suc (suc i)) = refl

extractPermutation : ∀ {n} → Fin (suc n) → Fin (suc n) ≃ Fin (suc n)
extractPermutation zero = idEquiv _
extractPermutation {n = suc n} (suc i) =
  compEquiv (isoToEquiv (iso swapFirst swapFirst swapFirst² swapFirst²))
    (liftPermutation (extractPermutation i))

extract-zero : ∀ {n} (i : Fin (suc n)) → equivFun (extractPermutation i) zero ≡ i
extract-zero zero = refl
extract-zero {n = suc n} (suc i) = cong suc (extract-zero i)

extract-lookup : ∀ {ℓ n} {A : Type ℓ} (xs : Vec A (suc n)) i k →
  lookup k (lookup i xs ∷ drop i xs) ≡ lookup (equivFun (extractPermutation i) k) xs
extract-lookup (x ∷ xs) zero k = refl
extract-lookup {n = suc n} (x ∷ xs) (suc i) zero =
  cong (λ j → lookup j xs) (sym (extract-zero i))
extract-lookup {n = suc n} (x ∷ xs) (suc i) (suc zero) = refl
extract-lookup {n = suc n} (x ∷ xs) (suc i) (suc (suc k)) =
  extract-lookup xs i (suc k)

private
  removeZero : ∀ {n} (i : Fin (suc n)) → (i ≡ zero → ⊥.⊥) → Fin n
  removeZero zero unequal = ⊥.rec (unequal refl)
  removeZero (suc i) unequal = i

  restoreZero : ∀ {n} (i : Fin (suc n)) (unequal : i ≡ zero → ⊥.⊥) →
    suc (removeZero i unequal) ≡ i
  restoreZero zero unequal = ⊥.rec (unequal refl)
  restoreZero (suc i) unequal = refl

  injective : ∀ {n} (σ : Fin n ≃ Fin n) {i j} → equivFun σ i ≡ equivFun σ j → i ≡ j
  injective σ {i} {j} = isoFunInjective (equivToIso σ) i j

  tailMap : ∀ {n} (σ : Fin (suc n) ≃ Fin (suc n)) → equivFun σ zero ≡ zero → Fin n → Fin n
  tailMap σ fixed i = removeZero (equivFun σ (suc i))
    (λ equal → snotz (injective σ (equal ∙ sym fixed)))

  tailMap-law : ∀ {n} (σ : Fin (suc n) ≃ Fin (suc n)) fixed i →
    suc (tailMap σ fixed i) ≡ equivFun σ (suc i)
  tailMap-law σ fixed i = restoreZero (equivFun σ (suc i)) _

  inverse-fixed : ∀ {n} (σ : Fin (suc n) ≃ Fin (suc n)) →
    equivFun σ zero ≡ zero → invEq σ zero ≡ zero
  inverse-fixed σ fixed = cong (invEq σ) (sym fixed) ∙ retEq σ zero

  tailMap-ret : ∀ {n} (σ : Fin (suc n) ≃ Fin (suc n)) fixed i →
    tailMap (invEquiv σ) (inverse-fixed σ fixed) (tailMap σ fixed i) ≡ i
  tailMap-ret σ fixed i = injSucFin
    (tailMap-law (invEquiv σ) (inverse-fixed σ fixed) (tailMap σ fixed i)
      ∙ cong (invEq σ) (tailMap-law σ fixed i) ∙ retEq σ (suc i))

tailPermutation : ∀ {n} (σ : Fin (suc n) ≃ Fin (suc n)) →
  equivFun σ zero ≡ zero → Fin n ≃ Fin n
tailPermutation σ fixed = isoToEquiv (iso
  (tailMap σ fixed) (tailMap (invEquiv σ) (inverse-fixed σ fixed))
  (λ i → injSucFin
    (tailMap-law σ fixed (tailMap (invEquiv σ) (inverse-fixed σ fixed) i)
      ∙ cong (equivFun σ) (tailMap-law (invEquiv σ) (inverse-fixed σ fixed) i)
      ∙ secEq σ (suc i)))
  (tailMap-ret σ fixed))

tailPermutation-law : ∀ {n} (σ : Fin (suc n) ≃ Fin (suc n)) fixed i →
  suc (equivFun (tailPermutation σ fixed) i) ≡ equivFun σ (suc i)
tailPermutation-law = tailMap-law

private
  normalized : ∀ {n} (σ : Fin (suc n) ≃ Fin (suc n)) → Fin (suc n) ≃ Fin (suc n)
  normalized σ = compEquiv σ (invEquiv (extractPermutation (equivFun σ zero)))

  normalized-zero : ∀ {n} (σ : Fin (suc n) ≃ Fin (suc n)) → equivFun (normalized σ) zero ≡ zero
  normalized-zero σ = cong (invEq (extractPermutation (equivFun σ zero)))
    (sym (extract-zero (equivFun σ zero))) ∙ retEq (extractPermutation (equivFun σ zero)) zero

removeMatchingPermutation : ∀ {n} → Fin (suc n) ≃ Fin (suc n) → Fin n ≃ Fin n
removeMatchingPermutation σ = tailPermutation (normalized σ) (normalized-zero σ)

removeMatching-law : ∀ {n} (σ : Fin (suc n) ≃ Fin (suc n)) i →
  equivFun (extractPermutation (equivFun σ zero))
    (suc (equivFun (removeMatchingPermutation σ) i)) ≡ equivFun σ (suc i)
removeMatching-law σ i =
  cong (equivFun (extractPermutation (equivFun σ zero)))
    (tailPermutation-law (normalized σ) (normalized-zero σ) i)
    ∙ secEq (extractPermutation (equivFun σ zero)) (equivFun σ (suc i))

removeMatching-lookup : ∀ {ℓ n} {A : Type ℓ} (xs : Vec A (suc n))
  (σ : Fin (suc n) ≃ Fin (suc n)) i →
  lookup (equivFun (removeMatchingPermutation σ) i) (drop (equivFun σ zero) xs) ≡
    lookup (equivFun σ (suc i)) xs
removeMatching-lookup xs σ i =
  extract-lookup xs (equivFun σ zero) (suc (equivFun (removeMatchingPermutation σ) i))
    ∙ cong (λ j → lookup j xs) (removeMatching-law σ i)
