module Cubical.Analysis.Real.Functions.Powers.Order where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ; zero; suc)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication


powPresIsNonnegative : ∀ x n →
  IsNonnegative x → IsNonnegative (powℝ x n)
powPresIsNonnegative x zero nonnegative =
  oneIsNonnegative
powPresIsNonnegative x (suc n) nonnegative =
  mulPresIsNonnegative x (powℝ x n)
    nonnegative (powPresIsNonnegative x n nonnegative)


powNonnegative : ∀ x n →
  0ℝ ≤ℝ x → 0ℝ ≤ℝ powℝ x n
powNonnegative x n 0≤x =
  isNonnegative→0≤ (powℝ x n)
    (powPresIsNonnegative x n
      (0≤→isNonnegative x 0≤x))


powMono : ∀ {x y} n →
  0ℝ ≤ℝ x → x ≤ℝ y →
  powℝ x n ≤ℝ powℝ y n
powMono zero 0≤x x≤y =
  ≤ℝ-refl 1ℝ
powMono {x} {y} (suc n) 0≤x x≤y =
  mulPres≤
    x y (powℝ x n) (powℝ y n)
    (≤ℝ-trans 0ℝ x y 0≤x x≤y)
    (powNonnegative x n 0≤x)
    x≤y
    (powMono n 0≤x x≤y)


absPow : ∀ x n →
  absℝ (powℝ x n) ≡ powℝ (absℝ x) n
absPow x zero = absOne
absPow x (suc n) =
  absMul x (powℝ x n)
  ∙ cong (absℝ x ·_) (absPow x n)


absPowMono : ∀ n x y →
  absℝ x ≤ℝ absℝ y →
  absℝ (powℝ x n) ≤ℝ absℝ (powℝ y n)
absPowMono n x y absx≤absy =
  subst2 _≤ℝ_
    (sym (absPow x n))
    (sym (absPow y n))
    (powMono n (absNonnegative x) absx≤absy)
