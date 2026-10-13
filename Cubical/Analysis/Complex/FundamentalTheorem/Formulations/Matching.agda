module Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Matching where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_; equivFun)
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.FinData using (Fin)
open import Cubical.Data.Vec using (Vec; lookup)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁)
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open import Cubical.Analysis.Real.Base using (ℝ; rat)
open import Cubical.Analysis.Real.Order.Base using (_≤ℝ_)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Norm using (normℂ)
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.Polynomial.Monic.Metric

-- Finite bijective matching retains multiplicities. The permutation is
-- truncated at each radius. Do not infer one exact permutation from all
-- radii, even if the associated products of linear factors are equal.
MatchingClose : ∀ {n} → Vec ℂ n → ℚ₊ → Vec ℂ n → Type₀
MatchingClose {n} roots ε roots′ = ∥ Σ[ σ ∈ (Fin n ≃ Fin n) ]
  ((i : Fin n) → lookup i roots ∼ℂ[ ε ] lookup (equivFun σ i) roots′) ∥₁

CoefficientsBounded : ∀ {n} → MonicPolynomial n → ℚ₊ → Type₀
CoefficientsBounded {n} p bound = (i : Fin n) → normℂ (lookup i p) ≤ℝ rat (fst bound)

RootsBounded : ∀ {n} → Vec ℂ n → ℚ₊ → Type₀
RootsBounded {n} roots bound = (i : Fin n) → normℂ (lookup i roots) ≤ℝ rat (fst bound)

-- Native quantitative counterpart of the matching estimates discussed in
-- Richman and Ruitenburg 3.10. This asks for the WHOLE modulus function.
-- Radiuswise truncated existence of δ would be a different statement.
RootMatchingEstimate : (ℕ → ℚ₊ → ℚ₊ → ℚ₊) → Type₀
RootMatchingEstimate matchingModulus = ∀ n bound ε (roots roots′ : Vec ℂ n) →
      CoefficientsBounded (linearFactors roots) bound →
      CoefficientsBounded (linearFactors roots′) bound →
      CoefficientCloseness (linearFactors roots) (matchingModulus n bound ε) (linearFactors roots′) →
      MatchingClose roots ε roots′

QuantitativeRootMatching : Type₀
QuantitativeRootMatching = Σ[ matchingModulus ∈ (ℕ → ℚ₊ → ℚ₊ → ℚ₊) ]
  RootMatchingEstimate matchingModulus

-- The other direction of continuity, on bounded root configurations.
FactorContinuityEstimate : (ℕ → ℚ₊ → ℚ₊ → ℚ₊) → Type₀
FactorContinuityEstimate factorModulus = ∀ n bound ε (roots roots′ : Vec ℂ n) →
      RootsBounded roots bound → RootsBounded roots′ bound →
      MatchingClose roots (factorModulus n bound ε) roots′ →
      CoefficientCloseness (linearFactors roots) ε (linearFactors roots′)

QuantitativeFactorContinuity : Type₀
QuantitativeFactorContinuity = Σ[ factorModulus ∈ (ℕ → ℚ₊ → ℚ₊ → ℚ₊) ]
  FactorContinuityEstimate factorModulus
