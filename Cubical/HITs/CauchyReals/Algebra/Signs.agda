module Cubical.HITs.CauchyReals.Algebra.Signs where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat as ℕ hiding (_·_; _+_)

import Cubical.Algebra.CommRing.Base as CommRing
import Cubical.Algebra.Ring.Properties as Ring
import Cubical.Algebra.OrderedCommRing.Properties as Ordered

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Algebra.Order.Instance
open import Cubical.HITs.CauchyReals.Foundation.Rationals

module ℚ→ℝSigns =
  Ring.RingHomTheory (CommRing.CommRingHom→RingHom ℚ→ℝHom)

module ℝOrder = Ordered.OrderedCommRingTheory ℝOrderedCommRing

-1ⁿ : ℕ → ℚ
-1ⁿ = ℚ.-1ⁿ

absᵣ[-1ⁿ]≡1 : ∀ n → absᵣ (rat (-1ⁿ n)) ≡ 1
absᵣ[-1ⁿ]≡1 n = absᵣ-rat _ ∙ cong rat (ℚ.abs[-1ⁿ]≡1 n)

-1ⁿ· : ℕ → ℝ → ℝ
-1ⁿ· = Rℝ.alternate

-1ⁿ·-suc : ∀ n x → -1ⁿ· (suc n) x ≡ -ᵣ (-1ⁿ· n x)
-1ⁿ·-suc = Rℝ.alternate-suc

-1ⁿ·-·2 : ∀ n x → -1ⁿ· (n ℕ.· 2) x ≡ x
-1ⁿ·-·2 = Rℝ.alternate-even

-1ⁿ-suc : ∀ n → rat (-1ⁿ (suc n)) ≡ -ᵣ (rat (-1ⁿ n))
-1ⁿ-suc n = cong rat (ℚ.-1ⁿ-suc n) ∙ sym (-ᵣ-rat _)

-1ⁿ·≡· : ∀ n x → -1ⁿ· n x ≡ rat (-1ⁿ n) ·ᵣ x
-1ⁿ·≡· n x =
  Rℝ.alternate≡alternatingSign· n x
  ∙ cong (_·ᵣ x) (sym (ℚ→ℝSigns.pres-alternatingSign n))

absᵣ∘-1ⁿ· : ∀ n x → absᵣ (-1ⁿ· n x) ≡ absᵣ x
absᵣ∘-1ⁿ· n x =
  abs-max _ ∙ ℝOrder.abs-alternate n x ∙ sym (abs-max x)
