module Cubical.HITs.CauchyReals.Algebra.Power.Base where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat as ℕ hiding (_·_; _+_)

import Cubical.Algebra.OrderedCommRing.Properties as Ordered

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Core
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Order.AbsoluteValue using (abs-max)
open import Cubical.HITs.CauchyReals.Algebra.Order.Instance using (ℝOrderedCommRing)
open import Cubical.HITs.CauchyReals.Foundation.Rationals

private
  module ℝOrder = Ordered.OrderedCommRingTheory ℝOrderedCommRing

0^ⁿ : ∀ n → 0 ^ⁿ (suc n) ≡ 0
0^ⁿ = Exponentiationᵣ.0^ˢⁿ≡0

1^ⁿ : ∀ n → 1 ^ⁿ n ≡ 1
1^ⁿ = Exponentiationᵣ.1ⁿ≡1

^ⁿ-odd : ∀ n x → -ᵣ (x ^ⁿ suc (n ℕ.· 2)) ≡ ((-ᵣ x) ^ⁿ suc (n ℕ.· 2))
^ⁿ-even : ∀ n x → (x ^ⁿ (n ℕ.· 2)) ≡ ((-ᵣ x) ^ⁿ (n ℕ.· 2))

^ⁿ-even = Exponentiationᵣ.^-even
^ⁿ-odd = Exponentiationᵣ.^-odd

x·x≡∣x∣·∣x∣ : ∀ x → x ·ᵣ x ≡ absᵣ x ·ᵣ absᵣ x
x·x≡∣x∣·∣x∣ x =
  sym (ℝOrder.abs²≡² x)
  ∙ cong₂ _·ᵣ_ (sym (abs-max x)) (sym (abs-max x))

IsContinuous^ⁿ : ∀ n → IsContinuous (_^ⁿ n)
IsContinuous^ⁿ zero = IsContinuousConst _
IsContinuous^ⁿ (suc n) =
  cont₂·ᵣ _ _ IsContinuousId (IsContinuous^ⁿ n)

0≤ᵣx² : ∀ x → 0 ≤ᵣ (x ^ⁿ 2)
0≤ᵣx² x =
  subst (0 ≤ᵣ_) (sym (x^²=x·x x)) (ℝOrder.0≤² x)

absᵣ^ⁿ : ∀ x n → absᵣ (x ^ⁿ n) ≡ (absᵣ x ^ⁿ n)
absᵣ^ⁿ x n =
  Exponentiationᵣ.dist·→dist^ absᵣ (absᵣ-rat 1) ·absᵣ n x

abs[x^²ⁿ] : ∀ n x → x ^ⁿ (n ℕ.· 2) ≡ absᵣ (x ^ⁿ (n ℕ.· 2))
abs[x^²ⁿ] zero x = sym (absᵣ-rat 1)
abs[x^²ⁿ] (suc n) x =
    ·ᵣAssoc _ _ _
  ∙ cong₂ _·ᵣ_ (x·x≡∣x∣·∣x∣ x) (abs[x^²ⁿ] n x)
  ∙ sym (·ᵣAssoc _ _ _)
  ∙ cong₂ _·ᵣ_ refl (sym (·absᵣ _ _))
  ∙ sym (·absᵣ _ _)
