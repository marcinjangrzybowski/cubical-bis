module Cubical.HITs.CauchyReals.Algebra.Order.Multiplication.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Data.Nat
open import Cubical.Data.Unit

open import Cubical.Algebra.OrderedCommRing.Properties

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Order.Instance


private
  module ℝOrder = OrderedCommRingTheory ℝOrderedCommRing


0<x^ⁿ : ∀ x n → 0 <ᵣ x → 0 <ᵣ x ^ⁿ n
0<x^ⁿ x n = ℝOrder.powPositive x n


0≤x^ⁿ : ∀ x n → 0 ≤ᵣ x → 0 ≤ᵣ x ^ⁿ n
0≤x^ⁿ x n = ℝOrder.powNonnegative x n


opaque

 <ᵣ₊Monotone·ᵣ : ∀ m n o s → 0 ≤ᵣ m → 0 ≤ᵣ o
   → m <ᵣ n → o <ᵣ s
   → m ·ᵣ o <ᵣ n ·ᵣ s
 <ᵣ₊Monotone·ᵣ m n o s 0≤m 0≤o =
   ℝOrder.·Mono< m n o s 0≤m 0≤o


 <≤ᵣ₊Monotone·ᵣ : ∀ (m : ℝ₀₊) n (o : ℝ₊) s
   → fst m <ᵣ n → fst o ≤ᵣ s
   → fst m ·ᵣ fst o <ᵣ n ·ᵣ s
 <≤ᵣ₊Monotone·ᵣ m n o s =
   ℝOrder.·Mono<≤ (fst m) n (fst o) s (snd m) (snd o)


 ≤<ᵣ₊Monotone·ᵣ : ∀ (m : ℝ₊) n (o : ℝ₀₊) s
   → fst m ≤ᵣ n → fst o <ᵣ s
   → fst m ·ᵣ fst o <ᵣ n ·ᵣ s
 ≤<ᵣ₊Monotone·ᵣ m n o s =
   ℝOrder.·Mono≤< (fst m) n (fst o) s (snd m) (snd o)


 z≤x≃y₊·z≤y₊·x : ∀ x z (y : ℝ₊) →
   (z ≤ᵣ x) ≃ (fst y ·ᵣ z ≤ᵣ fst y ·ᵣ x)
 z≤x≃y₊·z≤y₊·x x z y =
   ℝOrder.·MonoL≤≃ z x (fst y) (snd y)
