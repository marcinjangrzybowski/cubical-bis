module Cubical.Analysis.Real.Series.Uniform.Limit where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals.PositiveHalvesℚ using (_/4₊)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Sequence.Uniform
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Uniform

-- A uniform native Cauchy witness carries quantitative convergence data.
-- Its modulus is rescaled explicitly, using the completion's late-term
-- estimate. No family of pointwise convergence tails is selected.
opaque
  uniformlyCauchySeriesUniformLimitWitness : ∀ {ℓ} {A : Type ℓ}
    (terms : A → RealSequence) value → UniformlyCauchySeries A terms →
    UniformHasSum terms value → UniformLimitWitness (λ n x → partialSum (terms x) n) value
  uniformlyCauchySeriesUniformLimitWitness terms value native hasSum =
    PT.map (λ { (μ , close) → (λ ε → μ ((ε /4₊) /4₊)) , λ ε n large x →
      subst (partialSum (terms x) n ∼[ ε ]_)
        (canonicalLimit≡ (partialSum (terms x)) ∣ μ , close x ∣₁ (value x)
          (uniformHasSumAt hasSum x))
        (SP.close-lim-from-late (partialSum (terms x) n) (partialSum (terms x))
          ∣ μ , close x ∣₁ μ (close x) ε n large
          (refl∼ (partialSum (terms x) n) (((ε /4₊) /4₊) /4₊))) }) native
