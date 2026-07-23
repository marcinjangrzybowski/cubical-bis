module Cubical.HITs.CauchyReals.Complex.Modulus.MinkowskiRaw where

open import Cubical.Foundations.Prelude

import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.NatPlusOne

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Order.Positive
open import Cubical.HITs.CauchyReals.Transcendental.Roots.NonNegative
open import Cubical.HITs.CauchyReals.Analysis.Metric.PNorm.Base using (𝒑-norm×-lem)

open import Cubical.HITs.CauchyReals.Complex.Modulus.Triangle


asNonNeg : ∀ x → 0 ≤ᵣ x → ℝ₀₊
asNonNeg x 0≤x = x , 0≤x


opaque
  minkowskiSquaredRaw : ∀ a b c d
    → (0≤a : 0 ≤ᵣ a) → (0≤b : 0 ≤ᵣ b)
    → (0≤c : 0 ≤ᵣ c) → (0≤d : 0 ≤ᵣ d)
    → ((a +ᵣ c) ^ⁿ 2) +ᵣ ((b +ᵣ d) ^ⁿ 2) ≤ᵣ
      (fst (nth-rootNonNeg 2
        (powerNorm (asNonNeg a 0≤a) (asNonNeg b 0≤b))) +ᵣ
       fst (nth-rootNonNeg 2
        (powerNorm (asNonNeg c 0≤c) (asNonNeg d 0≤d)))) ^ⁿ 2
  minkowskiSquaredRaw a b c d 0≤a 0≤b 0≤c 0≤d =
    𝒑-norm×-lem 2 (ℕ.≤-refl)
      (asNonNeg a 0≤a) (asNonNeg c 0≤c)
      (asNonNeg b 0≤b) (asNonNeg d 0≤d)
