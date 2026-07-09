module Cubical.HITs.CauchyReals.Sequence.Limits where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma
open import Cubical.Data.Nat as ℕ hiding (_·_; _+_)
import Cubical.Data.Nat.Order as ℕ

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Closeness
open import Cubical.HITs.CauchyReals.Sequence

isCauchySequence-∘+ : ∀ s k
  → IsCauchySequence' s
  → IsCauchySequence' (s ∘ (k ℕ.+_))
isCauchySequence-∘+ s k =
  map-snd (λ X m n <n <m →
    X (k ℕ.+ m) (k ℕ.+ n)
      (ℕ.≤-trans <n ℕ.≤SumRight)
      (ℕ.≤-trans <m ℕ.≤SumRight)) ∘_

fromCauchySequence'₁-≡-lem : ∀ s ics ics' →
  fromCauchySequence'₁ s ics ≡ fromCauchySequence'₁ s ics'
fromCauchySequence'₁-≡-lem s =
  PT.elim2 (λ _ _ → isSetℝ _ _)
   (fromCauchySequence'-≡-lem s)

fromCauchySequence'₁-≡ : ∀ s s' ics ics' →
  (∀ n → s n ≡ s' n) →
  fromCauchySequence'₁ s ics ≡ fromCauchySequence'₁ s' ics'
fromCauchySequence'₁-≡ s s' ics ics' p = PT.elim2
  (λ ics ics' → isSetℝ
      (fromCauchySequence'₁ s ics)
      (fromCauchySequence'₁ s' ics'))
  (λ ics ics' → fromCauchySequence'-≡ s s' ics ics' p)
  ics ics'
