module Cubical.Analysis.Complex.FundamentalTheorem.Descent.Finite where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Modulus.Base
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.Polynomial.Translation

-- The Uniform module establishes this quantitative one-step property.
-- A strict upper bound also permits a zero constant coefficient.
PolynomialDescent : ℕ → ℝ → Type₀
PolynomialDescent n q = (p : MonicPolynomial (suc n)) (c : ℝ) →
  modulusℂ (evaluateMonic p 0ℂ) <ℝ c →
  ∥ Σ[ z ∈ ℂ ] modulusℂ (evaluateMonic p z) <ℝ q · c ∥₁

-- Every application of truncation elimination has a truncated target.
-- The recursion is finite; it constructs no selected infinite descent path.
finitePolynomialDescent : ∀ n q → PolynomialDescent n q →
  (p : MonicPolynomial (suc n)) (c : ℝ) →
  modulusℂ (evaluateMonic p 0ℂ) <ℝ c →
  (steps : ℕ) →
  ∥ Σ[ z ∈ ℂ ] modulusℂ (evaluateMonic p z) <ℝ powℝ q steps · c ∥₁
finitePolynomialDescent n q descend p c bound zero =
  ∣ 0ℂ , subst (modulusℂ (evaluateMonic p 0ℂ) <ℝ_) (sym (mulIdL c)) bound ∣₁
finitePolynomialDescent n q descend p c bound (suc steps) =
  PT.rec squash₁ improve (finitePolynomialDescent n q descend p c bound steps)
  where
  improve : (Σ[ z ∈ ℂ ] modulusℂ (evaluateMonic p z) <ℝ powℝ q steps · c) →
    ∥ Σ[ z ∈ ℂ ] modulusℂ (evaluateMonic p z) <ℝ powℝ q (suc steps) · c ∥₁
  improve (center , small) = PT.map
    (λ (z , smaller) → (center +ℂ z) ,
      subst2 _<ℝ_
        (cong modulusℂ (evaluate-translateMonic p center z))
        (mulAssoc q (powℝ q steps) c) smaller)
    (descend (translateMonic p center) (powℝ q steps · c)
      (subst (_<ℝ powℝ q steps · c)
        (sym (cong modulusℂ (translateMonic-atZero p center))) small))
