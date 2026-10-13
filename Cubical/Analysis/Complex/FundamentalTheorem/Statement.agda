module Cubical.Analysis.Complex.FundamentalTheorem.Statement where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.FinData using (Fin)
open import Cubical.Data.Vec using (Vec; lookup)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra using (0ℂ)
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.Polynomial.Monic.Metric public using (CoefficientCloseness)

ApproximateFactorization : ∀ {n} → MonicPolynomial n → ℚ₊ → Type₀
ApproximateFactorization {n} p ε =
  ∥ Σ[ roots ∈ Vec ℂ n ] CoefficientCloseness p ε (linearFactors roots) ∥₁

-- Inhabited by approximateFundamentalTheorem in the Approximate module.
-- Truncation stays inside the tolerance quantifier: it does not choose a
-- sequence of roots, a compatible ordering, or a native Cauchy witness.
ApproximateFundamentalTheorem : Type₀
ApproximateFundamentalTheorem =
  (n : ℕ) (p : MonicPolynomial n) (ε : ℚ₊) → ApproximateFactorization p ε

ExactFactorization : ∀ {n} → MonicPolynomial n → Type₀
ExactFactorization {n} p = ∥ Σ[ roots ∈ Vec ℂ n ] linearFactors roots ≡ p ∥₁

ApproximateRootExistence : Type₀
ApproximateRootExistence = (n : ℕ) (p : MonicPolynomial (suc n)) (ε : ℚ₊) →
  ∥ Σ[ z ∈ ℂ ] (evaluateMonic p z ∼ℂ[ ε ] 0ℂ) ∥₁
