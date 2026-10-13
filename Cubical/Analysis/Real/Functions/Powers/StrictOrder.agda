module Cubical.Analysis.Real.Functions.Powers.StrictOrder where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (zero; suc)
open import Cubical.Data.Nat.Literals
open import Cubical.Data.Rationals.Base using (fromNatℚ)
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Unit using (tt)
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Order.Strict.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Located
open import Cubical.Analysis.Real.Order.Strict.Continuity
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Functions.Powers.Order

powPositive : ∀ x n → 0ℝ <ℝ x → 0ℝ <ℝ powℝ x n
powPositive x zero positive = <ℚ→<ℝ 0 1 (ℚ.pos<pos tt)
powPositive x (suc n) positive = mulPositive x (powℝ x n) positive (powPositive x n positive)

powStrictMonoNonnegative : ∀ n x y → 0ℝ ≤ℝ x → x <ℝ y →
  powℝ x (suc n) <ℝ powℝ y (suc n)
powStrictMonoNonnegative n x y nonnegative less =
  ≤<ℝ-trans (x · powℝ x n) (x · powℝ y n) (y · powℝ y n)
    (mulPres≤L (powℝ x n) (powℝ y n) x (0≤→isNonnegative x nonnegative)
      (powMono n nonnegative (<ℝ-weaken x y less)))
    (mulPres<PosR x y (powℝ y n)
      (powPositive y n (≤<ℝ-trans 0ℝ x y nonnegative less)) less)

powReflects≤Nonnegative : ∀ n x y → 0ℝ ≤ℝ y →
  powℝ x (suc n) ≤ℝ powℝ y (suc n) → x ≤ℝ y
powReflects≤Nonnegative n x y nonnegative powers = notGreater→≤ℝ x y λ greater →
  ≤ℝ→≯ (powℝ x (suc n)) (powℝ y (suc n)) powers
    (powStrictMonoNonnegative n y x nonnegative greater)

powReflects<Nonnegative : ∀ n x y → 0ℝ ≤ℝ y →
  powℝ x (suc n) <ℝ powℝ y (suc n) → x <ℝ y
powReflects<Nonnegative n x y nonnegative powers =
  continuousReflectsStrictOnOrderedInputs (λ z → powℝ z (suc n)) (pow-isContinuous (suc n))
    x y (powReflects≤Nonnegative n x y nonnegative
      (<ℝ-weaken (powℝ x (suc n)) (powℝ y (suc n)) powers)) powers

powInjectiveNonnegative : ∀ n x y → 0ℝ ≤ℝ x → 0ℝ ≤ℝ y →
  powℝ x (suc n) ≡ powℝ y (suc n) → x ≡ y
powInjectiveNonnegative n x y xp yp equation = ≤ℝ-antisym x y
  (powReflects≤Nonnegative n x y yp
    (subst (_≤ℝ powℝ y (suc n)) (sym equation) (≤ℝ-refl (powℝ y (suc n)))))
  (powReflects≤Nonnegative n y x xp
    (subst (_≤ℝ powℝ x (suc n)) equation (≤ℝ-refl (powℝ x (suc n)))))
