module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicContinuous.Laws.Neg.Sequence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation as Neg
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannSum.DyadicRecursive

opaque
  dyadicRecursiveSum-neg-function : ∀ f a b →
    dyadicRecursiveSum (Neg.-_ ∘ f) a b
      ≡ Neg.-_ ∘ dyadicRecursiveSum f a b
  dyadicRecursiveSum-neg-function f a b =
    funExt (dyadicRecursiveSum-neg f a b)
