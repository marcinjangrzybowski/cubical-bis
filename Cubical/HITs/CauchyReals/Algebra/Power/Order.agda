module Cubical.HITs.CauchyReals.Algebra.Power.Order where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat as ℕ hiding (_·_; _+_)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Rationals as ℚ using (ℚ)
open import Cubical.Data.Rationals.Order as ℚ

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Order.Multiplication
open import Cubical.HITs.CauchyReals.Analysis.Sequence.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals hiding (_^_)

-- Previous name: ℚ^ⁿ-Monotone⁻¹.
ℚ^ⁿ-reflects-≤ : ∀ {x y : ℚ} n → 0 ℕ.< n →
  0 ℚ.≤ x → 0 ℚ.≤ y →
  ℚ._^ⁿ_ x n ℚ.≤ ℚ._^ⁿ_ y n → x ℚ.≤ y
ℚ^ⁿ-reflects-≤ {x} {y} n 0<n 0≤x 0≤y xⁿ≤yⁿ =
  ℚ.≮→≥ y x
    (ℚ.≤→≯ (ℚ._^ⁿ_ x n) (ℚ._^ⁿ_ y n) xⁿ≤yⁿ ∘
      ℚ^ⁿ-StrictMonotone n 0<n 0≤y 0≤x)

-- Previous name: ^ⁿ-StrictMonotoneR.
^ⁿ-strictlyIncreasingExponent : ∀ {x : ℝ} m n →
  1 <ᵣ x → m ℕ.< n → x ^ⁿ m <ᵣ x ^ⁿ n
^ⁿ-strictlyIncreasingExponent m zero 1<x m<n =
  ⊥.rec (ℕ.¬-<-zero m<n)
^ⁿ-strictlyIncreasingExponent {x} zero (suc n) 1<x m<n =
  1<^ x n 1<x
^ⁿ-strictlyIncreasingExponent {x} (suc m) (suc n) 1<x sm<sn =
  subst2 _<ᵣ_
    (·ᵣComm (x ^ⁿ m) x)
    (·ᵣComm (x ^ⁿ n) x)
    (<ᵣ-·ᵣo _ _
      (x , isTrans<ᵣ 0 1 x (<ℚ→<ᵣ 0 1 ℚ.decℚ<?) 1<x)
      (^ⁿ-strictlyIncreasingExponent m n 1<x
        (ℕ.predℕ-≤-predℕ sm<sn)))
