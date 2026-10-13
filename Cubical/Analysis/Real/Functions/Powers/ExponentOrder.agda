module Cubical.Analysis.Real.Functions.Powers.ExponentOrder where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (zero; suc; _+_)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Algebra.CommRing
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Functions.Powers.Order

private
  multiplyPowers : ∀ x m n → powℝ x m · powℝ x n ≡ powℝ x (m + n)
  multiplyPowers x zero n = mulIdL (powℝ x n)
  multiplyPowers x (suc m) n = sym (mulAssoc x (powℝ x m) (powℝ x n))
    ∙ cong (x ·_) (multiplyPowers x m n)

powBelowOne : ∀ x n → 0ℝ ≤ℝ x → x ≤ℝ 1ℝ → powℝ x n ≤ℝ 1ℝ
powBelowOne x zero nonnegative below = ≤ℝ-refl 1ℝ
powBelowOne x (suc n) nonnegative below = subst (powℝ x (suc n) ≤ℝ_) (mulIdR 1ℝ)
  (mulPres≤ x 1ℝ (powℝ x n) 1ℝ (isNonnegative→0≤ 1ℝ oneIsNonnegative)
    (powNonnegative x n nonnegative) below (powBelowOne x n nonnegative below))

powPositiveExponent≤Base : ∀ x n → 0ℝ ≤ℝ x → x ≤ℝ 1ℝ → powℝ x (suc n) ≤ℝ x
powPositiveExponent≤Base x n nonnegative below =
  subst (powℝ x (suc n) ≤ℝ_) (mulIdR x)
    (mulPres≤L (powℝ x n) 1ℝ x (0≤→isNonnegative x nonnegative)
      (powBelowOne x n nonnegative below))

powAntitoneExponent : ∀ x m n → 0ℝ ≤ℝ x → x ≤ℝ 1ℝ → m ℕ.≤ n → powℝ x n ≤ℝ powℝ x m
powAntitoneExponent x m n nonnegative below (gap , equation) =
  subst2 _≤ℝ_ (multiplyPowers x gap m ∙ cong (powℝ x) equation) (mulIdL (powℝ x m))
    (mulPres≤R-0≤ (powℝ x gap) 1ℝ (powℝ x m) (powNonnegative x m nonnegative)
      (powBelowOne x gap nonnegative below))
