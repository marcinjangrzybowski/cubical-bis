module Cubical.Analysis.Complex.FundamentalTheorem.Clusters.Matching where

-- All sufficiently accurate factorizations of one polynomial match.
-- The whole tolerance function is constructed from one coefficient bound;
-- neither a root ordering nor a family of approximations is selected.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Vec using (Vec)
open import Cubical.Data.Sigma
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveRationals.PositiveHalvesℚ using (_/2₊)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.Polynomial.Monic.Metric
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Matching
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.RootMatching
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.ApproximateEquivalence
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.Coefficients

FactorMatchingAt : ∀ {n} → MonicPolynomial n → (ℚ₊ → ℚ₊) → Type₀
FactorMatchingAt {n} p μ = ∀ ε (roots roots′ : Vec ℂ n) →
  CoefficientCloseness p (μ ε) (linearFactors roots) →
  CoefficientCloseness p (μ ε) (linearFactors roots′) → MatchingClose roots ε roots′

factorMatchingRadius : ℕ → ℚ₊ → ℚ₊ → ℚ₊
factorMatchingRadius n A ε = min₊ 1 (rootMatchingModulus n (A +₊ (1 +₊ 1)) ε /2₊)

opaque
  factorMatchingAt-bound : ∀ {n} (p : MonicPolynomial n) A →
    CoefficientsBounded p A → FactorMatchingAt p (factorMatchingRadius n A)
  factorMatchingAt-bound {n} p A bounded ε roots roots′ first second =
    rootMatchingEstimate n B ε roots roots′
      (nearbyCoefficient-bound p (linearFactors roots) A bounded
        (coefficientCloseness-monotone p (linearFactors roots) δ 1 (min₊≤L 1 half) first))
      (nearbyCoefficient-bound p (linearFactors roots′) A bounded
        (coefficientCloseness-monotone p (linearFactors roots′) δ 1 (min₊≤L 1 half) second))
      (coefficientCloseness-halfTriangle (linearFactors roots) p (linearFactors roots′)
        (rootMatchingModulus n B ε)
        (coefficientCloseness-sym p (linearFactors roots) half
          (coefficientCloseness-monotone p (linearFactors roots) δ half (min₊≤R 1 half) first))
        (coefficientCloseness-monotone p (linearFactors roots′) δ half (min₊≤R 1 half) second))
    where
    B half δ : ℚ₊
    B = A +₊ (1 +₊ 1)
    half = rootMatchingModulus n B ε /2₊
    δ = factorMatchingRadius n A ε

  factorMatchingAt : ∀ {n} (p : MonicPolynomial n) →
    PT.∥ Σ[ μ ∈ (ℚ₊ → ℚ₊) ] FactorMatchingAt p μ ∥₁
  factorMatchingAt {n} p = PT.map
    (λ { (A , bounded) → factorMatchingRadius n A , factorMatchingAt-bound p A bounded })
    (coefficientBound-exists p)
