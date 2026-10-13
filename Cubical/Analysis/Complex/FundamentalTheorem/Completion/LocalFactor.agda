open import Cubical.Data.Nat using (ℕ)

module Cubical.Analysis.Complex.FundamentalTheorem.Completion.LocalFactor (n : ℕ) where

-- A single nearby finite configuration bounds a whole neighborhood of a
-- completed multiset. The resulting WHOLE factor modulus is constructed
-- before truncation, as required by the native completion lifting route.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (equivFun; invEq)
open import Cubical.Data.Vec using (Vec; lookup; map)
open import Cubical.Data.Sigma
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveRationals.PositiveHalvesℚ using (_/2₊)
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Polynomial.Monic.Metric
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Presented
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Matching
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Completion
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.FactorContinuity
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.ApproximateEquivalence
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.Gaussian
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.Base
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.Density
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.Bounds

module R = MatchingCompletion (rootMultisetCompletion n)

opaque
  inserted→matching : ∀ (qs rs : Vec GaussianRational n) ε →
    R.insert qs R.near[ ε ] R.insert rs → MatchingClose (map gaussianℂ qs) ε (map gaussianℂ rs)
  inserted→matching qs rs ε close = PT.map
    (λ { (σ , matched) → σ , λ i → subst2 (λ z w → z ∼ℂ[ ε ] w)
      (sym (lookup-gaussian qs i)) (sym (lookup-gaussian rs (equivFun σ i))) (matched i) })
    (equivFun (R.insertionIsometry qs rs ε) close)

  matching→inserted : ∀ (qs rs : Vec GaussianRational n) ε →
    MatchingClose (map gaussianℂ qs) ε (map gaussianℂ rs) → R.insert qs R.near[ ε ] R.insert rs
  matching→inserted qs rs ε close = invEq (R.insertionIsometry qs rs ε)
    (PT.map (λ { (σ , matched) → σ , λ i → subst2 (λ z w → z ∼ℂ[ ε ] w)
      (lookup-gaussian qs i) (lookup-gaussian rs (equivFun σ i)) (matched i) }) close)

FactorCenteredAt : R.Carrier → (ℚ₊ → ℚ₊) → Type₀
FactorCenteredAt x μ = ∀ ε (qs rs : Vec GaussianRational n) →
  R.insert qs R.near[ μ ε ] x → R.insert rs R.near[ μ ε ] x →
  CoefficientCloseness (gaussianFactors qs) ε (gaussianFactors rs)

opaque
  factor-centered : ∀ x → PT.∥ Σ[ μ ∈ (ℚ₊ → ℚ₊) ] FactorCenteredAt x μ ∥₁
  factor-centered x = PT.rec PT.isPropPropTrunc
    (λ { (qs , close) → PT.map (withBound qs close) (coefficientBound-exists (map gaussianℂ qs)) })
    (R.dense x 1)
    where
    withBound : ∀ qs → R.insert qs R.near[ 1 ] x →
      (Σ[ B ∈ ℚ₊ ] RootsBounded (map gaussianℂ qs) B) →
      Σ[ μ ∈ (ℚ₊ → ℚ₊) ] FactorCenteredAt x μ
    withBound qs center (B , bounded) = μ , preserve
      where
      A : ℚ₊
      A = B +₊ ((1 +₊ 1) +₊ (1 +₊ 1))

      μ : ℚ₊ → ℚ₊
      μ ε = min₊ 1 (factorContinuityModulus n A ε /2₊)

      neighborBound : ∀ ε rs → R.insert rs R.near[ μ ε ] x → RootsBounded (map gaussianℂ rs) A
      neighborBound ε rs close = matching-nearby-bound (map gaussianℂ qs) (map gaussianℂ rs) B (1 +₊ 1)
        bounded (inserted→matching qs rs (1 +₊ 1)
          (R.isTriangular≈ (R.insert qs) x (R.insert rs) 1 1 center
            (R.isSym≈ (R.insert rs) x 1
              (R.isMonotone≈≤ (R.insert rs) x (μ ε) 1
                (min₊≤L 1 (factorContinuityModulus n A ε /2₊)) close))))

      preserve : FactorCenteredAt x μ
      preserve ε rs ss near-r near-s = factorContinuityEstimate n A ε (map gaussianℂ rs) (map gaussianℂ ss)
        (neighborBound ε rs near-r) (neighborBound ε ss near-s)
        (inserted→matching rs ss (factorContinuityModulus n A ε)
          (R.subst≈ (R.insert rs) (R.insert ss)
            (1/2∈ℚ./2+/2≡id (fst (factorContinuityModulus n A ε)))
            (R.isTriangular≈ (R.insert rs) x (R.insert ss)
              (factorContinuityModulus n A ε /2₊) (factorContinuityModulus n A ε /2₊)
              (R.isMonotone≈≤ (R.insert rs) x (μ ε) (factorContinuityModulus n A ε /2₊)
                (min₊≤R 1 (factorContinuityModulus n A ε /2₊)) near-r)
              (R.isSym≈ (R.insert ss) x (factorContinuityModulus n A ε /2₊)
                (R.isMonotone≈≤ (R.insert ss) x (μ ε) (factorContinuityModulus n A ε /2₊)
                  (min₊≤R 1 (factorContinuityModulus n A ε /2₊)) near-s)))))
