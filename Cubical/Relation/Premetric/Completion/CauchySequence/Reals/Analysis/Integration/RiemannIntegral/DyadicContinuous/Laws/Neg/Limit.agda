module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicContinuous.Laws.Neg.Limit where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation as Neg
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base using (_≤ℝ_)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Sequence
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.UniformContinuity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicContinuous.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicContinuous.Laws.Neg.Sequence

opaque
  negatedDyadicRecursiveSumHasLimit :
    ∀ a b (a≤b : a ≤ℝ b) f
    (f-uc : IsRadiuswiseUniformlyContinuousℝ f) →
    HasRecursiveDyadicIntegral (Neg.-_ ∘ f) a b
      (Neg.- recursiveDyadicIntegral f a b a≤b f-uc)
  negatedDyadicRecursiveSumHasLimit a b a≤b f f-uc =
    subst
      (λ sequence → isLimitSequence sequence
        (Neg.- recursiveDyadicIntegral f a b a≤b f-uc))
      (sym (dyadicRecursiveSum-neg-function f a b))
      (negPresIsLimitSequence
        (recursiveDyadicIntegralHasLimit f a b a≤b f-uc))
