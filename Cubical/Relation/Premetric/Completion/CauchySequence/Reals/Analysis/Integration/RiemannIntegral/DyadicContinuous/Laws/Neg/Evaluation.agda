module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicContinuous.Laws.Neg.Evaluation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation as Neg
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base using (_≤ℝ_)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.UniformContinuity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicContinuous.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicContinuous.Base.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicContinuous.Laws.Neg.Definition
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicContinuous.Laws.Neg.Limit

opaque
  recursiveDyadicIntegralNeg-evaluation :
    ∀ a b (a≤b : a ≤ℝ b) f
    (f-uc : IsRadiuswiseUniformlyContinuousℝ f) →
    recursiveDyadicIntegralNeg a b a≤b f f-uc
      ≡ Neg.- recursiveDyadicIntegral f a b a≤b f-uc
  recursiveDyadicIntegralNeg-evaluation a b a≤b f f-uc =
    recursiveDyadicIntegral-unique-sealed
      (Neg.-_ ∘ f) a b a≤b
      (negatedFunctionIsRadiuswiseUniformlyContinuous f f-uc)
      (Neg.- recursiveDyadicIntegral f a b a≤b f-uc)
      (negatedDyadicRecursiveSumHasLimit a b a≤b f f-uc)
