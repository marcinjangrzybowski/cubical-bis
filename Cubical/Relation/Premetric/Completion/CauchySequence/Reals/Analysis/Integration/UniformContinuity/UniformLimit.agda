module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.UniformContinuity.UniformLimit where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveHalvesℚ

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

open import Cubical.Relation.Premetric.Base

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Uniform
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.UniformContinuity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.UniformContinuity.Operations


-- A uniform limit of radiuswise uniformly continuous partial sums remains
-- radiuswise uniformly continuous.  At each output radius we open exactly
-- one uniform-convergence cutoff and one radius for that finite partial sum;
-- no modulus function and no sequence of moduli is selected.

uniformSeriesValueIsRadiuswiseUniformlyContinuousFromPartialSums :
  ∀ {ℓ ℓ'} {X : Type ℓ}
  (source : PremetricStr ℓ' X)
  (terms : X → RealSequence)
  (uniform : UniformlyCauchySeries X terms) →
  (∀ n → IsRadiuswiseUniformlyContinuous
    source (λ x → partialSum (terms x) n)
    (snd Real.ℝPremetricSpace)) →
  IsRadiuswiseUniformlyContinuous
    source (uniformSeriesValue X terms uniform)
    (snd Real.ℝPremetricSpace)
uniformSeriesValueIsRadiuswiseUniformlyContinuousFromPartialSums
  {X = X} source terms uniform partial-sum-uniform ε =
  PT.rec squash₁ use-uniform-cutoff
    (uniformPartialSumsConvergeToSeriesValue
      X terms uniform (ε /4₊))
  where
  value : X → Real.ℝ
  value = uniformSeriesValue X terms uniform

  use-uniform-cutoff :
    (Σ[ N ∈ ℕ ]
      (∀ x n → N ℕ.≤ n →
        partialSum (terms x) n Real.Base.≈ᶜ[ ε /4₊ ] value x)) →
    ∃[ δ ∈ ℚ₊ ]
      (∀ x y → PremetricStr._≈[_]_ source x δ y →
        value x Real.Base.≈ᶜ[ ε ] value y)
  use-uniform-cutoff (N , close-to-value) =
    PT.map use-partial-sum-radius
      (partial-sum-uniform N (ε /2₊))
    where
    use-partial-sum-radius :
      (Σ[ δ ∈ ℚ₊ ]
        (∀ x y → PremetricStr._≈[_]_ source x δ y →
          partialSum (terms x) N Real.Base.≈ᶜ[ ε /2₊ ]
            partialSum (terms y) N)) →
      Σ[ δ ∈ ℚ₊ ]
        (∀ x y → PremetricStr._≈[_]_ source x δ y →
          value x Real.Base.≈ᶜ[ ε ] value y)
    use-partial-sum-radius (δ , partial-close) =
      δ , λ x y x≈y →
        subst
          (λ radius → value x Real.Base.≈ᶜ[ radius ] value y)
          (ℚ₊≡ ℚ!)
          (Real.Approximation.tri≈ᶜ
            (value x) (partialSum (terms x) N) (value y)
            (ε /4₊) ((ε /2₊) +₊ (ε /4₊))
            (Real.Base.sym≈ᶜ
              (partialSum (terms x) N) (value x) (ε /4₊)
              (close-to-value x N ℕ.≤-refl))
            (Real.Approximation.tri≈ᶜ
              (partialSum (terms x) N)
              (partialSum (terms y) N) (value y)
              (ε /2₊) (ε /4₊)
              (partial-close x y x≈y)
              (close-to-value y N ℕ.≤-refl)))


uniformSeriesValueIsRadiuswiseUniformlyContinuous :
  ∀ {ℓ ℓ'} {X : Type ℓ}
  (source : PremetricStr ℓ' X)
  (terms : X → RealSequence)
  (uniform : UniformlyCauchySeries X terms) →
  (∀ n → IsRadiuswiseUniformlyContinuous
    source (λ x → terms x n)
    (snd Real.ℝPremetricSpace)) →
  IsRadiuswiseUniformlyContinuous
    source (uniformSeriesValue X terms uniform)
    (snd Real.ℝPremetricSpace)
uniformSeriesValueIsRadiuswiseUniformlyContinuous
  source terms uniform term-uniform =
  uniformSeriesValueIsRadiuswiseUniformlyContinuousFromPartialSums
    source terms uniform
    (partialSumFamilyIsRadiuswiseUniformlyContinuous
      source terms term-uniform)
