module Cubical.Analysis.Complex.FundamentalTheorem.Descent.ErrorAllowance where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.Inverse.Positive
open import Cubical.Analysis.Real.Algebra.Inverse.Order
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Functions.Powers.Order
open import Cubical.Analysis.Real.Functions.Powers.StrictOrder
open import Cubical.Analysis.Real.Functions.Powers.ExponentOrder

module PowerErrorAllowance (n : ℕ) (q : ℝ) (positive : 0ℝ <ℝ q) (ε : ℝ) where
  private
    factor = powℝ q (suc n)
    factor-positive = powPositive q (suc n) positive
    reciprocal = positiveReciprocal factor factor-positive

  opaque
    allowance : ℝ
    allowance = reciprocal · ε

    allowance-formula : allowance ≡ positiveReciprocal (powℝ q (suc n)) (powPositive q (suc n) positive) · ε
    allowance-formula = refl

    allowance-equation : factor · allowance ≡ ε
    allowance-equation = mulAssoc factor reciprocal ε
      ∙ cong (_· ε) (positiveReciprocalLaw factor factor-positive) ∙ mulIdL ε

    allowance-nonnegative : 0ℝ ≤ℝ ε → 0ℝ ≤ℝ allowance
    allowance-nonnegative nonnegative = isNonnegative→0≤ allowance
      (mulPresIsNonnegative reciprocal ε
        (0≤→isNonnegative reciprocal (<ℝ-weaken 0ℝ reciprocal (positiveReciprocalPositive factor factor-positive)))
        (0≤→isNonnegative ε nonnegative))

  allowance-expands : q ≤ℝ 1ℝ → 0ℝ ≤ℝ ε → ε ≤ℝ allowance
  allowance-expands small nonnegative = subst2 _≤ℝ_ allowance-equation (mulIdL allowance)
    (mulPres≤R-0≤ factor 1ℝ allowance (allowance-nonnegative nonnegative)
      (powBelowOne q (suc n) (<ℝ-weaken 0ℝ q positive) small))

  allowance-scaled : ∀ i → i ℕ.≤ n → q ≤ℝ 1ℝ → 0ℝ ≤ℝ ε → ε ≤ℝ powℝ q (suc i) · allowance
  allowance-scaled i degree small nonnegative = subst (_≤ℝ powℝ q (suc i) · allowance) allowance-equation
    (mulPres≤R-0≤ factor (powℝ q (suc i)) allowance (allowance-nonnegative nonnegative)
      (powAntitoneExponent q (suc i) (suc n) (<ℝ-weaken 0ℝ q positive) small (ℕ.suc-≤-suc degree)))
