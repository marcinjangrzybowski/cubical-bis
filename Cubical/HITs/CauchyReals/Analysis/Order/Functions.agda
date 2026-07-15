module Cubical.HITs.CauchyReals.Analysis.Order.Functions where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base

IsStrictlyIncreasingOn :
  (P : ℙ ℝ) → (∀ x → x ∈ P → ℝ) → Type
IsStrictlyIncreasingOn P f =
  ∀ x (x∈ : x ∈ P) y (y∈ : y ∈ P) →
    x <ᵣ y → f x x∈ <ᵣ f y y∈

IsNondecreasingOn :
  (P : ℙ ℝ) → (∀ x → x ∈ P → ℝ) → Type
IsNondecreasingOn P f =
  ∀ x (x∈ : x ∈ P) y (y∈ : y ∈ P) →
    x ≤ᵣ y → f x x∈ ≤ᵣ f y y∈
