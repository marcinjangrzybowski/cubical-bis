module Cubical.Analysis.Complex.Series.PowerSeries.Translation.Algebra where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc; _∸_)
import Cubical.Data.Nat as Nat
import Cubical.Data.Nat.Order as Nat
open import Cubical.Data.FinData using (toℕ; toℕ<n)
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.BinomialThm
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Tactics.CommRingSolver

-- Finite rearrangements are checked over an abstract ring, keeping native
-- completed real arithmetic out of normalization.
module TranslationAlgebra {ℓ} (R : CommRing ℓ) where
  open CommRingStr (snd R)
  open Exponentiation R
  private
    module B = BinomialThm R
    module S = Sum (CommRing→Ring R)

  cancelRightWithInverse : ∀ x y c inverse → c · inverse ≡ 1r → x · c ≡ y · c → x ≡ y
  cancelRightWithInverse x y c inverse unit equal = sym (·IdR x)
    ∙ cong (x ·_) (sym unit) ∙ ·Assoc x c inverse
    ∙ cong (_· inverse) equal ∙ sym (·Assoc y c inverse)
    ∙ cong (y ·_) unit ∙ ·IdR y

  opaque
    normalizeDerivativeTerm : ∀ e p a z → e · ((p · a) · z) ≡ ((e · p) · a) · z
    normalizeDerivativeTerm e p a z = solve! R

    binomialTerm : ∀ b a x y → ((b · a) · y) · x ≡ a · ((b · x) · y)
    binomialTerm b a x y = solve! R

  opaque
    translatedMonomialAddition : (coefficients : ℕ → fst R) (binomial : ℕ → ℕ → fst R) →
      (∀ n k → binomial n k ≡ B._choose_ n k) → ∀ center increment n →
      S.∑ {n = suc n} (λ k →
        ((binomial ((n ∸ toℕ k) Nat.+ toℕ k) (toℕ k) · coefficients ((n ∸ toℕ k) Nat.+ toℕ k))
          · (center ^ (n ∸ toℕ k))) · (increment ^ toℕ k))
        ≡ coefficients n · ((center + increment) ^ n)
    translatedMonomialAddition coefficients binomial agrees center increment n =
      S.∑Ext (λ k → summand (toℕ k) (Nat.pred-≤-pred (toℕ<n k)))
      ∙ sym (S.∑Mulrdist (coefficients n) (B.BinomialVec n increment center))
      ∙ cong (coefficients n ·_) (sym (B.BinomialThm n increment center)
        ∙ cong (_^ n) (+Comm increment center))
      where
      summand : ∀ k → k Nat.≤ n →
        ((binomial ((n ∸ k) Nat.+ k) k · coefficients ((n ∸ k) Nat.+ k)) · (center ^ (n ∸ k))) · (increment ^ k)
          ≡ coefficients n · ((B._choose_ n k · (increment ^ k)) · (center ^ (n ∸ k)))
      summand k below = cong
        (λ total → ((binomial total k · coefficients total) · (center ^ (n ∸ k))) · (increment ^ k))
        (Nat.[n-m]+m k n below)
        ∙ cong (λ b → ((b · coefficients n) · (center ^ (n ∸ k))) · (increment ^ k)) (agrees n k)
        ∙ binomialTerm (B._choose_ n k) (coefficients n) (increment ^ k) (center ^ (n ∸ k))
