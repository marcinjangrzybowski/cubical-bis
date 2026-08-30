module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicContinuous.Base.Sealed where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base using (_≤ℝ_)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicContinuous.Base


opaque
  recursiveDyadicIntegral-independent-sealed :
    ∀ f a b (a≤b : a ≤ℝ b) (a≤b' : a ≤ℝ b) f-uc f-uc' →
    recursiveDyadicIntegral f a b a≤b f-uc
      ≡ recursiveDyadicIntegral f a b a≤b' f-uc'
  recursiveDyadicIntegral-independent-sealed =
    recursiveDyadicIntegral-independent

  recursiveDyadicIntegral-unique-sealed :
    ∀ f a b (a≤b : a ≤ℝ b) f-uc value →
    HasRecursiveDyadicIntegral f a b value →
    recursiveDyadicIntegral f a b a≤b f-uc ≡ value
  recursiveDyadicIntegral-unique-sealed = recursiveDyadicIntegral-unique
