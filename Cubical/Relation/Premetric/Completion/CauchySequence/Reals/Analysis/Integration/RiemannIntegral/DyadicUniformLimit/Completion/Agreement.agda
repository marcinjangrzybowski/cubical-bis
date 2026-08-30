module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicUniformLimit.Completion.Agreement where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Sequence
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.UniformContinuity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicContinuous.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicUniformLimit.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicUniformLimit.Preservation.Global
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicUniformLimit.Completion.Cauchy
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicUniformLimit.Completion.Definition


-- Completing the integral sequence independently gives the same value as
-- integrating the uniform limit.

completedUniformIntegral-agrees :
  ∀ functions value a b (a≤b : a ≤ℝ b)
  (functions-uc : ∀ n →
    IsRadiuswiseUniformlyContinuousℝ (functions n))
  (uniform : UniformlyConvergesFunctionSequence functions value) →
  completedUniformIntegral
    functions value a b a≤b functions-uc uniform
  ≡
  recursiveDyadicIntegral value a b a≤b
    (uniformLimitIsRadiuswiseUniformlyContinuous
      functions value functions-uc uniform)
completedUniformIntegral-agrees
  functions value a b a≤b functions-uc uniform =
  canonicalLimit≡
    (λ n → recursiveDyadicIntegral
      (functions n) a b a≤b (functions-uc n))
    (uniformIntegralSequenceIsCauchy
      functions value a b a≤b functions-uc uniform)
    (recursiveDyadicIntegral value a b a≤b
      (uniformLimitIsRadiuswiseUniformlyContinuous
        functions value functions-uc uniform))
    (recursiveDyadicIntegralPresUniformLimit
      functions value a b a≤b functions-uc uniform)
