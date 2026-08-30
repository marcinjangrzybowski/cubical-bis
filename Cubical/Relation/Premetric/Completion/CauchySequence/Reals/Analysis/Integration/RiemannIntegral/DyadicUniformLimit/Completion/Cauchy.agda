module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicUniformLimit.Completion.Cauchy where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Sequence
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.UniformContinuity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicContinuous.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicUniformLimit.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicUniformLimit.Preservation.Global


-- Uniform convergence therefore makes the sequence of integrals Cauchy in
-- the native completion, without selecting a convergence modulus.

uniformIntegralSequenceIsCauchy :
  ∀ functions value a b (a≤b : a ≤ℝ b)
  (functions-uc : ∀ n →
    IsRadiuswiseUniformlyContinuousℝ (functions n))
  (uniform : UniformlyConvergesFunctionSequence functions value) →
  IsCauchySequence
    (λ n → recursiveDyadicIntegral
      (functions n) a b a≤b (functions-uc n))
uniformIntegralSequenceIsCauchy
  functions value a b a≤b functions-uc uniform =
  isLimitSequence→isCauchySequence
    (recursiveDyadicIntegralPresUniformLimit
      functions value a b a≤b functions-uc uniform)
