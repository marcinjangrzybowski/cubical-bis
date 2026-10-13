module Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Presented where

-- Representation-sensitive formulations. Input names are explicit data;
-- no theorem here asserts that all native reals admit such names.
-- Compare Ruitenburg 3.13 and Peshev--Skordev (2006).

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
import Cubical.Data.Nat.Order as Nat
open import Cubical.Data.FinData using (Fin)
open import Cubical.Data.Vec using (Vec; lookup)
open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Base using (ℚ)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁)
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open import Cubical.Analysis.Real.Base using (rat)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra using (0ℂ)
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Polynomial.Monic

GaussianRational : Type₀
GaussianRational = ℚ × ℚ

gaussianℂ : GaussianRational → ℂ
gaussianℂ (a , b) = rat a , rat b

record RationalPresentationℂ (z : ℂ) : Type₀ where
  field
    approximants : ℕ → GaussianRational
    modulus : ℚ₊ → ℕ
    converges : ∀ ε k → modulus ε Nat.≤ k → gaussianℂ (approximants k) ∼ℂ[ ε ] z

CoefficientPresentations : ∀ {n} → MonicPolynomial n → Type₀
CoefficientPresentations {n} p = (i : Fin n) → RationalPresentationℂ (lookup i p)

PresentedRoot : ∀ {n} → MonicPolynomial n → Type₀
PresentedRoot p = Σ[ z ∈ ℂ ] ((evaluateMonic p z ≡ 0ℂ) × RationalPresentationℂ z)

PresentedExactRootExistence : Type₀
PresentedExactRootExistence = (n : ℕ) (p : MonicPolynomial (suc n)) →
  CoefficientPresentations p → ∥ PresentedRoot p ∥₁

-- Stronger algorithmic output: a root and its name, rather than truncated
-- existence. The function may depend on the input names. We do not require
-- it to respect replacement of those names by other names of the same p.
PresentedRootAlgorithm : Type₀
PresentedRootAlgorithm = (n : ℕ) (p : MonicPolynomial (suc n)) →
  CoefficientPresentations p → PresentedRoot p

PresentedExactFactorization : ∀ {n} → MonicPolynomial n → Type₀
PresentedExactFactorization {n} p = ∥ Σ[ roots ∈ Vec ℂ n ]
  ((linearFactors roots ≡ p) × ((i : Fin n) → RationalPresentationℂ (lookup i roots))) ∥₁

PresentedFundamentalTheorem : Type₀
PresentedFundamentalTheorem = (n : ℕ) (p : MonicPolynomial n) →
  CoefficientPresentations p → PresentedExactFactorization p
