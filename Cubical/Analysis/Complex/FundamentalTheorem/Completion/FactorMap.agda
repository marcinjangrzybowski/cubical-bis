open import Cubical.Data.Nat using (ℕ)

module Cubical.Analysis.Complex.FundamentalTheorem.Completion.FactorMap (n : ℕ) where

-- The canonical factor map is an embedding with dense image, continuous
-- in both directions on its image. Correspondence establishes surjectivity
-- separately; density alone is not promoted to a chosen family of rational
-- factorizations.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.Polynomial.Monic.Metric
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.Density
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.LocalFactor n using (module R)
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.Graph n
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.GraphContinuity n
open import Cubical.Analysis.Complex.FundamentalTheorem.Completion.Extension n

opaque
  completedFactors-injective : ∀ x y → completedFactors x ≡ completedFactors y → x ≡ y
  completedFactors-injective x y equal = joint-roots-unique x y (completedFactors x)
    (completedFactors-joint x) (subst (Joint y) (sym equal) (completedFactors-joint y))

  completedFactors-continuity : ∀ x → PT.∥ Σ[ μ ∈ (ℚ₊ → ℚ₊) ]
    (∀ ε y → x R.near[ μ ε ] y → CoefficientCloseness (completedFactors x) ε (completedFactors y)) ∥₁
  completedFactors-continuity x = PT.map
    (λ { (μ , preserve) → μ , λ ε y close → preserve ε y (completedFactors x) (completedFactors y)
      (completedFactors-joint x) (completedFactors-joint y) close }) (joint-factor-continuity x)

  -- This is the inverse modulus on the image, with no surjectivity premise.
  completedFactors-inverse-continuity : ∀ x → PT.∥ Σ[ μ ∈ (ℚ₊ → ℚ₊) ]
    (∀ ε y → CoefficientCloseness (completedFactors x) (μ ε) (completedFactors y) → x R.near[ ε ] y) ∥₁
  completedFactors-inverse-continuity x = PT.map
    (λ { (μ , preserve) → μ , λ ε y close → preserve ε x y (completedFactors y)
      (completedFactors-joint x) (completedFactors-joint y) close }) (joint-root-continuity (completedFactors x))

  completedFactors-dense : ∀ p ε → PT.∥ Σ[ x ∈ R.Carrier ] CoefficientCloseness p ε (completedFactors x) ∥₁
  completedFactors-dense p ε = PT.map
    (λ { (qs , close) → R.insert qs , subst (CoefficientCloseness p ε)
      (sym (completedFactors-insert qs)) close }) (gaussian-factor-density n p ε)
