module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicUniformLimit.Preservation.Local where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Inverse
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveHalvesℚ

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Archimedean
  using (RationalBound ; ∃rationalBound)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Sequence
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.UniformContinuity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicContinuous.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicUniformLimit.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicUniformLimit.Integral.PointwiseClose


-- Only interval-local uniform convergence is needed for convergence of the
-- integrals.  Continuity of the limit is kept explicit here, allowing the
-- local theorem to be used even when convergence is not global.

recursiveDyadicIntegralPresUniformLimitOn :
  ∀ functions value a b (a≤b : a ≤ℝ b)
  (functions-uc : ∀ n →
    IsRadiuswiseUniformlyContinuousℝ (functions n))
  (value-uc : IsRadiuswiseUniformlyContinuousℝ value) →
  UniformlyConvergesFunctionSequenceOn a b functions value →
  isLimitSequence
    (λ n → recursiveDyadicIntegral
      (functions n) a b a≤b (functions-uc n))
    (recursiveDyadicIntegral value a b a≤b value-uc)
recursiveDyadicIntegralPresUniformLimitOn
  functions value a b a≤b functions-uc value-uc uniform ε =
  PT.rec squash₁ with-width-bound (∃rationalBound (b Group.- a))
  where
  with-width-bound :
    RationalBound (b Group.- a) →
    ∃[ N ∈ ℕ ]
      (∀ n → N ℕ.≤ n →
        recursiveDyadicIntegral
          (functions n) a b a≤b (functions-uc n)
          Real.Base.≈ᶜ[ ε ]
        recursiveDyadicIntegral value a b a≤b value-uc)
  with-width-bound (B , width-bound) =
    PT.map
      (λ { (N , close) →
        N , λ n N≤n →
          recursiveDyadicIntegral-pointwiseClose
            a b a≤b B (functions n) value
            (functions-uc n) value-uc ε width-bound
            (λ x a≤x x≤b → close x a≤x x≤b n N≤n) })
      (uniform (((ε /2₊) /2₊) ₊／₊ B))
