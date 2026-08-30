module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicUniformLimit.Completion.Definition where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Sequence
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.UniformContinuity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicContinuous.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicUniformLimit.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicUniformLimit.Completion.Cauchy


completedUniformIntegral :
  ∀ functions value a b (a≤b : a ≤ℝ b)
  (functions-uc : ∀ n →
    IsRadiuswiseUniformlyContinuousℝ (functions n)) →
  UniformlyConvergesFunctionSequence functions value →
  Real.ℝ
completedUniformIntegral
  functions value a b a≤b functions-uc uniform =
  limitOfCauchySequence
    (λ n → recursiveDyadicIntegral
      (functions n) a b a≤b (functions-uc n))
    (uniformIntegralSequenceIsCauchy
      functions value a b a≤b functions-uc uniform)
