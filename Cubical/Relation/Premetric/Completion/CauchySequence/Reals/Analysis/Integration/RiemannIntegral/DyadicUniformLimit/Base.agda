module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicUniformLimit.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveHalvesℚ
open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.UniformContinuity


-- Uniform convergence keeps one common cutoff under truncation at each
-- requested radius.  It is deliberately a property, rather than a chosen
-- modulus, so it matches the native Cauchy-sequence completion interface.

UniformlyConvergesFunctionSequence :
  (ℕ → Real.ℝ → Real.ℝ) → (Real.ℝ → Real.ℝ) → Type₀
UniformlyConvergesFunctionSequence functions value =
  ∀ ε →
    ∃[ N ∈ ℕ ]
      (∀ x n → N ℕ.≤ n →
        functions n x Real.Base.≈ᶜ[ ε ] value x)


isPropUniformlyConvergesFunctionSequence : ∀ functions value →
  isProp (UniformlyConvergesFunctionSequence functions value)
isPropUniformlyConvergesFunctionSequence functions value =
  isPropΠ λ _ → squash₁


-- Integration only samples the closed interval.  This local variant is the
-- useful interface for power-series and other functions whose convergence
-- need not be uniform on the whole real line.

UniformlyConvergesFunctionSequenceOn :
  Real.ℝ → Real.ℝ →
  (ℕ → Real.ℝ → Real.ℝ) → (Real.ℝ → Real.ℝ) → Type₀
UniformlyConvergesFunctionSequenceOn a b functions value =
  ∀ ε →
    ∃[ N ∈ ℕ ]
      (∀ x → a ≤ℝ x → x ≤ℝ b →
        ∀ n → N ℕ.≤ n →
          functions n x Real.Base.≈ᶜ[ ε ] value x)


isPropUniformlyConvergesFunctionSequenceOn : ∀ a b functions value →
  isProp (UniformlyConvergesFunctionSequenceOn a b functions value)
isPropUniformlyConvergesFunctionSequenceOn a b functions value =
  isPropΠ λ _ → squash₁


uniformlyConvergesFunctionSequence→on :
  ∀ a b functions value →
  UniformlyConvergesFunctionSequence functions value →
  UniformlyConvergesFunctionSequenceOn a b functions value
uniformlyConvergesFunctionSequence→on a b functions value uniform ε =
  PT.map
    (λ { (N , close) →
      N , λ x _ _ n N≤n → close x n N≤n })
    (uniform ε)


-- Unlike the series-specific closure theorem, this applies to any uniformly
-- convergent function sequence.  At one output radius it opens one common
-- convergence cutoff and one radius for a single approximant.

uniformLimitIsRadiuswiseUniformlyContinuous :
  ∀ functions value →
  (∀ n → IsRadiuswiseUniformlyContinuousℝ (functions n)) →
  UniformlyConvergesFunctionSequence functions value →
  IsRadiuswiseUniformlyContinuousℝ value
uniformLimitIsRadiuswiseUniformlyContinuous
  functions value functions-uc uniform ε =
  PT.rec squash₁ use-approximant (uniform (ε /4₊))
  where
  use-approximant :
    Σ[ N ∈ ℕ ]
      (∀ x n → N ℕ.≤ n →
        functions n x Real.Base.≈ᶜ[ ε /4₊ ] value x) →
    ∃[ δ ∈ ℚ₊ ]
      (∀ x y → x Real.Base.≈ᶜ[ δ ] y →
        value x Real.Base.≈ᶜ[ ε ] value y)
  use-approximant (N , close-to-value) =
    PT.map use-radius (functions-uc N (ε /2₊))
    where
    use-radius :
      Σ[ δ ∈ ℚ₊ ]
        (∀ x y → x Real.Base.≈ᶜ[ δ ] y →
          functions N x Real.Base.≈ᶜ[ ε /2₊ ] functions N y) →
      Σ[ δ ∈ ℚ₊ ]
        (∀ x y → x Real.Base.≈ᶜ[ δ ] y →
          value x Real.Base.≈ᶜ[ ε ] value y)
    use-radius (δ , approximant-close) =
      δ , λ x y x≈y →
        subst
          (λ radius → value x Real.Base.≈ᶜ[ radius ] value y)
          (ℚ₊≡ ℚ!)
          (Real.Approximation.tri≈ᶜ
            (value x) (functions N x) (value y)
            (ε /4₊) ((ε /2₊) +₊ (ε /4₊))
            (Real.Base.sym≈ᶜ
              (functions N x) (value x) (ε /4₊)
              (close-to-value x N ℕ.≤-refl))
            (Real.Approximation.tri≈ᶜ
              (functions N x) (functions N y) (value y)
              (ε /2₊) (ε /4₊)
              (approximant-close x y x≈y)
              (close-to-value y N ℕ.≤-refl)))
