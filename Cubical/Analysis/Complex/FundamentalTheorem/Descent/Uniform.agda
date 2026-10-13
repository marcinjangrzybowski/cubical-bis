module Cubical.Analysis.Complex.FundamentalTheorem.Descent.Uniform where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (suc)
open import Cubical.Data.FinData using (zero)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Located
open import Cubical.Analysis.Real.Order.Strict.Multiplication
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Modulus.Base
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.Polynomial.Expansion
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.Finite
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.Factor
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.Positive

-- Locatedness either makes zero already sufficient, or supplies the
-- positive constant modulus needed by angular cancellation.
uniformPolynomialDescent : ∀ n → PolynomialDescent n (descentContraction n)
uniformPolynomialDescent n p c initial-bound = PT.rec squash₁ fromComparison
  (dichotomyℝ 0ℝ A (q · c) (mulPositive q c (descentContraction-positive n) c-positive))
  where
  A = modulusℂ (monicCoefficient p zero)
  q = descentContraction n

  atZero : modulusℂ (evaluateMonic p 0ℂ) ≡ A
  atZero = cong modulusℂ (evaluateMonic-atZero p)

  constant-bound : A <ℝ c
  constant-bound = subst (_<ℝ c) atZero initial-bound

  c-positive : 0ℝ <ℝ c
  c-positive = ≤<ℝ-trans 0ℝ A c (modulusℂ-nonnegative (monicCoefficient p zero)) constant-bound

  fromComparison : (A <ℝ q · c) ⊎ (0ℝ <ℝ A) →
    ∥ Σ[ z ∈ ℂ ] modulusℂ (evaluateMonic p z) <ℝ q · c ∥₁
  fromComparison (inl small) = ∣ 0ℂ , subst (_<ℝ q · c) (sym atZero) small ∣₁
  fromComparison (inr positive) = PT.map
    (λ (z , improvement) → z , <ℝ-trans (modulusℂ (evaluateMonic p z)) (q · A) (q · c) improvement
      (mulPres<PosL A c q (descentContraction-positive n) constant-bound))
    (positiveConstantDescent p positive)
