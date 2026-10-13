module Cubical.Analysis.Complex.FundamentalTheorem.Completion.Density where

-- Products of Gaussian-rational linear factors are coefficient-dense.
-- Each requested accuracy uses one approximate factorization and finitely
-- many rational approximations, all inside propositional truncation.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (idEquiv)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.FinData using (Fin)
open import Cubical.Data.Vec using (Vec; map; lookup)
open import Cubical.Data.Sigma
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveRationals.PositiveHalvesℚ using (_/2₊)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Metric.Operations
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.Polynomial.Monic.Metric
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Presented
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Matching
open import Cubical.Analysis.Complex.FundamentalTheorem.Approximate
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.Scale
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.Coefficients
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.FactorContinuity
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.ApproximateEquivalence
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.Gaussian

gaussianFactors : ∀ {n} → Vec GaussianRational n → MonicPolynomial n
gaussianFactors qs = linearFactors (map gaussianℂ qs)

opaque
  gaussian-factors-approximate : ∀ {n} (xs : Vec ℂ n) ε →
    PT.∥ Σ[ qs ∈ Vec GaussianRational n ] CoefficientCloseness (linearFactors xs) ε (gaussianFactors qs) ∥₁
  gaussian-factors-approximate {n} xs ε = PT.rec PT.isPropPropTrunc withBound (coefficientBound-exists xs)
    where
    withBound : (Σ[ B ∈ ℚ₊ ] RootsBounded xs B) →
      PT.∥ Σ[ qs ∈ Vec GaussianRational n ] CoefficientCloseness (linearFactors xs) ε (gaussianFactors qs) ∥₁
    withBound (B , bounded) = PT.map approximate (gaussian-vector-dense xs δ)
      where
      A δ : ℚ₊
      A = B +₊ (1 +₊ 1)
      δ = min₊ 1 (factorContinuityModulus n A ε)

      approximate : (Σ[ qs ∈ Vec GaussianRational n ] CoefficientCloseness (map gaussianℂ qs) δ xs) →
        Σ[ qs ∈ Vec GaussianRational n ] CoefficientCloseness (linearFactors xs) ε (gaussianFactors qs)
      approximate (qs , close) = qs , factorContinuityEstimate n A ε xs (map gaussianℂ qs)
        (coefficientNorm-monotone xs ⟦ B ⟧₊ ⟦ A ⟧₊ (radius-sumL B (1 +₊ 1)) bounded)
        (nearbyCoefficient-bound xs (map gaussianℂ qs) B bounded
          (coefficientCloseness-monotone xs (map gaussianℂ qs) δ 1
            (min₊≤L 1 (factorContinuityModulus n A ε)) reverse-close))
        PT.∣ idEquiv (Fin n) ,
          coefficientCloseness-monotone xs (map gaussianℂ qs) δ (factorContinuityModulus n A ε)
            (min₊≤R 1 (factorContinuityModulus n A ε)) reverse-close ∣₁
        where
        reverse-close : CoefficientCloseness xs δ (map gaussianℂ qs)
        reverse-close i = sym∼ℂ (lookup i (map gaussianℂ qs)) (lookup i xs) δ (close i)

  gaussian-factor-density : ∀ n (p : MonicPolynomial n) ε →
    PT.∥ Σ[ qs ∈ Vec GaussianRational n ] CoefficientCloseness p ε (gaussianFactors qs) ∥₁
  gaussian-factor-density n p ε = PT.rec PT.isPropPropTrunc
    (λ { (xs , close) → PT.map
      (λ { (qs , approximate) → qs , coefficientCloseness-halfTriangle p
        (linearFactors xs) (gaussianFactors qs) ε close approximate })
      (gaussian-factors-approximate xs (ε /2₊)) })
    (approximateFundamentalTheorem n p (ε /2₊))
