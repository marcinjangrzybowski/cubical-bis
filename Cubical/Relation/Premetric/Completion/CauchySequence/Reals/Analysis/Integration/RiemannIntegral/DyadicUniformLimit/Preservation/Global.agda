module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicUniformLimit.Preservation.Global where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Sequence
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.UniformContinuity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicContinuous.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicUniformLimit.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicUniformLimit.Preservation.Local


-- The completed dyadic integral commutes with arbitrary uniformly convergent
-- sequences of radiuswise uniformly continuous functions.  The continuity
-- witness for the limit is constructed in Base; completeness and the uniform
-- width estimate then supply convergence of the integral values directly.

recursiveDyadicIntegralPresUniformLimit :
  ∀ functions value a b (a≤b : a ≤ℝ b)
  (functions-uc : ∀ n →
    IsRadiuswiseUniformlyContinuousℝ (functions n))
  (uniform : UniformlyConvergesFunctionSequence functions value) →
  isLimitSequence
    (λ n → recursiveDyadicIntegral
      (functions n) a b a≤b (functions-uc n))
    (recursiveDyadicIntegral value a b a≤b
      (uniformLimitIsRadiuswiseUniformlyContinuous
        functions value functions-uc uniform))
recursiveDyadicIntegralPresUniformLimit
  functions value a b a≤b functions-uc uniform ε =
  recursiveDyadicIntegralPresUniformLimitOn
    functions value a b a≤b functions-uc
    (uniformLimitIsRadiuswiseUniformlyContinuous
      functions value functions-uc uniform)
    (uniformlyConvergesFunctionSequence→on
      a b functions value uniform)
    ε
