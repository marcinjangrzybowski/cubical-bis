module Cubical.HITs.CauchyReals.Signs where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat as ℕ hiding (_·_; _+_)

open import Cubical.HITs.CauchyReals.Base
open import Cubical.HITs.CauchyReals.Order
open import Cubical.HITs.CauchyReals.Continuous
open import Cubical.HITs.CauchyReals.Multiplication
open import Cubical.HITs.CauchyReals.Inverse
open import Cubical.HITs.CauchyReals.RationalsImports

-1ⁿ : ℕ → ℚ
-1ⁿ zero = 1
-1ⁿ (suc zero) = -1
-1ⁿ (suc (suc n)) = -1ⁿ n

absᵣ[-1ⁿ]≡1 : ∀ n → absᵣ (rat (-1ⁿ n)) ≡ 1
absᵣ[-1ⁿ]≡1 zero = absᵣ-rat _
absᵣ[-1ⁿ]≡1 (suc zero) = absᵣ-rat _
absᵣ[-1ⁿ]≡1 (suc (suc n)) = absᵣ[-1ⁿ]≡1 n

-1ⁿ· : ℕ → ℝ → ℝ
-1ⁿ· zero x = x
-1ⁿ· (suc zero) = -ᵣ_
-1ⁿ· (suc (suc n)) = -1ⁿ· n

-1ⁿ·-suc : ∀ n x → -1ⁿ· (suc n) x ≡ -ᵣ (-1ⁿ· n x)
-1ⁿ·-suc zero x = refl
-1ⁿ·-suc (suc zero) x = sym (-ᵣInvol x)
-1ⁿ·-suc (suc (suc n)) x = -1ⁿ·-suc n x

-1ⁿ·-·2 : ∀ n x → -1ⁿ· (n ℕ.· 2) x ≡ x
-1ⁿ·-·2 zero x = refl
-1ⁿ·-·2 (suc n) x = -1ⁿ·-·2 n x

-1ⁿ-suc : ∀ n → rat (-1ⁿ (suc n)) ≡ -ᵣ (rat (-1ⁿ n))
-1ⁿ-suc zero = sym (-ᵣ-rat _)
-1ⁿ-suc (suc zero) = sym (-ᵣ-rat _)
-1ⁿ-suc (suc (suc n)) = -1ⁿ-suc n

-1ⁿ·≡· : ∀ n x → -1ⁿ· n x ≡ rat (-1ⁿ n) ·ᵣ x
-1ⁿ·≡· zero x = sym (·IdLᵣ _)
-1ⁿ·≡· (suc zero) x = -ᵣ≡[-1·ᵣ] _
-1ⁿ·≡· (suc (suc n)) x = -1ⁿ·≡· n x

absᵣ∘-1ⁿ· : ∀ n x → absᵣ (-1ⁿ· n x) ≡ absᵣ x
absᵣ∘-1ⁿ· zero x = refl
absᵣ∘-1ⁿ· (suc zero) x = sym (-absᵣ _)
absᵣ∘-1ⁿ· (suc (suc n)) x = absᵣ∘-1ⁿ· n x
