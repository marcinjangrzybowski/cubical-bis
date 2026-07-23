module Cubical.HITs.CauchyReals.Algebra.Power.Order where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Nat as ℕ hiding (_·_; _+_)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Rationals as ℚ using (ℚ)
open import Cubical.Data.Rationals.Order as ℚ

import Cubical.Algebra.OrderedCommRing.Properties as Ordered
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals using
  (ℚOrderedCommRing)

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Order.Apartness using (_＃_)
open import Cubical.HITs.CauchyReals.Algebra.Order.Instance using
  (ℝOrderedCommRing)
open import Cubical.HITs.CauchyReals.Foundation.Rationals hiding (_^_)

private
  module ℝOrder = Ordered.OrderedCommRingTheory ℝOrderedCommRing
  module ℚOrder = Ordered.OrderedCommRingTheory ℚOrderedCommRing

1<^ : ∀ x n → 1 <ᵣ x → 1 <ᵣ x ^ⁿ suc n
1<^ = ℝOrder.one<pow

^<1 : ∀ x → 0 ≤ᵣ x → ∀ n → x <ᵣ 1 → x ^ⁿ suc n <ᵣ 1
^<1 = ℝOrder.pow<one

^≤1 : ∀ x → 0 ≤ᵣ x → ∀ n → x ≤ᵣ 1 → x ^ⁿ n ≤ᵣ 1
^≤1 = ℝOrder.pow≤one

1＃^ : ∀ x → 0 ≤ᵣ x → ∀ n → (1 ＃ x) → (1 ＃ (x ^ⁿ suc n))
1＃^ = ℝOrder.one#pow

^ⁿ-StrictMonotone : ∀ {x y : ℝ} n → 0 ℕ.< n
  → 0 ≤ᵣ x → 0 ≤ᵣ y → x <ᵣ y → x ^ⁿ n <ᵣ y ^ⁿ n
^ⁿ-StrictMonotone = ℝOrder.powStrictMono

^ⁿ-Monotone : ∀ {x y : ℝ} n
  → 0 ≤ᵣ x → x ≤ᵣ y → x ^ⁿ n ≤ᵣ y ^ⁿ n
^ⁿ-Monotone = ℝOrder.powMono

^ⁿ-reflects-≤ : ∀ {x y : ℝ} n → 0 ℕ.< n
  → 0 ≤ᵣ x → 0 ≤ᵣ y → x ^ⁿ n ≤ᵣ y ^ⁿ n → x ≤ᵣ y
^ⁿ-reflects-≤ = ℝOrder.powReflects≤

-- Previous home: Analysis.Sequence.Base.
^ⁿMonotone⁻¹ : ∀ {x y : ℝ} n → 0 ℕ.< n → 0 <ᵣ x → 0 <ᵣ y
  → x ^ⁿ n ≤ᵣ y ^ⁿ n → x ≤ᵣ y
^ⁿMonotone⁻¹ n 0<n 0<x 0<y =
  ^ⁿ-reflects-≤ n 0<n
    (<ᵣWeaken≤ᵣ _ _ 0<x) (<ᵣWeaken≤ᵣ _ _ 0<y)

-- Previous home: Analysis.Sequence.Base.
opaque
  ^ⁿMonotone⁻¹-with0 : ∀ {x y : ℝ} n → 0 ℕ.< n → 0 ≤ᵣ x → 0 <ᵣ y
    → x ^ⁿ n ≤ᵣ y ^ⁿ n → x ≤ᵣ y
  ^ⁿMonotone⁻¹-with0 n 0<n 0≤x 0<y =
    ^ⁿ-reflects-≤ n 0<n 0≤x (<ᵣWeaken≤ᵣ _ _ 0<y)

ℚ^ⁿ-Monotone : ∀ {x y : ℚ} n →
  0 ℚ.≤ x → 0 ℚ.≤ y → x ℚ.≤ y →
  ℚ._^ⁿ_ x n ℚ.≤ ℚ._^ⁿ_ y n
ℚ^ⁿ-Monotone n 0≤x _ x≤y = ℚOrder.powMono n 0≤x x≤y

ℚ^ⁿ-StrictMonotone : ∀ {x y : ℚ} n → 0 ℕ.< n →
  0 ℚ.≤ x → 0 ℚ.≤ y → x ℚ.< y →
  ℚ._^ⁿ_ x n ℚ.< ℚ._^ⁿ_ y n
ℚ^ⁿ-StrictMonotone = ℚOrder.powStrictMono

-- Previous name: ℚ^ⁿ-Monotone⁻¹.
ℚ^ⁿ-reflects-≤ : ∀ {x y : ℚ} n → 0 ℕ.< n →
  0 ℚ.≤ x → 0 ℚ.≤ y →
  ℚ._^ⁿ_ x n ℚ.≤ ℚ._^ⁿ_ y n → x ℚ.≤ y
ℚ^ⁿ-reflects-≤ = ℚOrder.powReflects≤

-- Previous name: ^ⁿ-StrictMonotoneR.
^ⁿ-strictlyIncreasingExponent : ∀ {x : ℝ} m n →
  1 <ᵣ x → m ℕ.< n → x ^ⁿ m <ᵣ x ^ⁿ n
^ⁿ-strictlyIncreasingExponent = ℝOrder.powExponentStrictMono

-- Previous home: Trigonometry.Pi.
^ⁿ-MonotoneR-inv : ∀ x → 0 ≤ᵣ x → x ≤ᵣ 1 → ∀ m n →
  m ℕ.≤ n → x ^ⁿ n ≤ᵣ x ^ⁿ m
^ⁿ-MonotoneR-inv = ℝOrder.powExponentAntitone
