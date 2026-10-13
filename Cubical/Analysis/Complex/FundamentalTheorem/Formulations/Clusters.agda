module Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Clusters where

-- Small separated spectra without presupposing a constructed root-multiset
-- space. Strict diameter and separation are expressed on sufficiently close
-- finite factorizations. Approximate FTA makes these tests nonvacuous.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.Data.FinData using (Fin)
open import Cubical.Data.Vec using (Vec; []; _∷_; lookup)
import Cubical.Data.List as List
open import Cubical.Data.Sigma
open import Cubical.Data.Empty using (⊥)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁)
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open import Cubical.Analysis.Real.Base using (rat)
open import Cubical.Analysis.Real.Order.Base using (_≤ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Modulus.Base using (modulusℂ)
open import Cubical.Analysis.Complex.Polynomial.Base
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.Polynomial.Monic.Metric
open import Cubical.Analysis.Complex.Polynomial.Differential.Monic
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Basic using (PolynomialIdentityℂ)

SpectrumDiameterBelow : ∀ {n} → MonicPolynomial n → ℚ₊ → Type₀
SpectrumDiameterBelow {n} p ε = ∥ Σ[ δ ∈ ℚ₊ ]
  ((roots : Vec ℂ n) → CoefficientCloseness p δ (linearFactors roots) →
    (i j : Fin n) → modulusℂ (lookup i roots -ℂ lookup j roots) <ℝ rat (fst ε)) ∥₁

SpectraSeparated : ∀ {m n} → MonicPolynomial m → MonicPolynomial n → Type₀
SpectraSeparated {m} {n} p q = ∥ Σ[ gap ∈ ℚ₊ ] Σ[ δ ∈ ℚ₊ ]
  ((roots : Vec ℂ m) (roots′ : Vec ℂ n) →
    CoefficientCloseness p δ (linearFactors roots) →
    CoefficientCloseness q δ (linearFactors roots′) →
    (i : Fin m) (j : Fin n) →
      rat (fst gap) ≤ℝ modulusℂ (lookup i roots -ℂ lookup j roots′)) ∥₁

PositiveMonicPolynomial : Type₀
PositiveMonicPolynomial = Σ[ d ∈ ℕ ] MonicPolynomial (suc d)

clusterDegree : ∀ {k} → Vec PositiveMonicPolynomial k → ℕ
clusterDegree [] = zero
clusterDegree ((d , p) ∷ factors) = suc d + clusterDegree factors

clusterProduct : ∀ {k} → Vec PositiveMonicPolynomial k → List.List ℂ
clusterProduct [] = 1ℂ List.∷ List.[]
clusterProduct ((d , p) ∷ factors) = multiplyPolynomialsℂ (monicCoefficients p) (clusterProduct factors)

ClusterConditions : ∀ {n k} → MonicPolynomial n → ℚ₊ → Vec PositiveMonicPolynomial k → Type₀
ClusterConditions {n} {k} p ε factors =
  (clusterDegree factors ≡ n) ×
  PolynomialIdentityℂ (clusterProduct factors) (monicCoefficients p) ×
  ((i : Fin k) → SpectrumDiameterBelow (snd (lookup i factors)) ε) ×
  ((i j : Fin k) → (i ≡ j → ⊥) → SpectraSeparated (snd (lookup i factors)) (snd (lookup j factors)))

ClusterFactorizationData : ∀ {n} → MonicPolynomial n → ℚ₊ → Type₀
ClusterFactorizationData p ε = Σ[ k ∈ ℕ ] Σ[ factors ∈ Vec PositiveMonicPolynomial k ]
  ClusterConditions p ε factors

-- Lubarsky--Richman 3.2, adapted to native coefficient and metric APIs.
-- Factors have positive degree, but are NOT required to be linear.
SmallSeparatedFactorization : Type₀
SmallSeparatedFactorization = (n : ℕ) (p : MonicPolynomial n) (ε : ℚ₊) →
  ∥ ClusterFactorizationData p ε ∥₁
