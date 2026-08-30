module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicContinuous.Laws.Add where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition as Add
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base using (_≤ℝ_)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Sequence
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.UniformContinuity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.UniformContinuity.Operations using (addIsRadiuswiseUniformlyContinuous)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannSum.DyadicRecursive
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicContinuous.Base

recursiveDyadicIntegral-add :
  ∀ a b (a≤b : a ≤ℝ b) f g
  (f-uc : IsRadiuswiseUniformlyContinuousℝ f)
  (g-uc : IsRadiuswiseUniformlyContinuousℝ g) →
  recursiveDyadicIntegral
    (λ x → f x Add.+ g x) a b a≤b
    (addIsRadiuswiseUniformlyContinuous
      (snd Real.ℝPremetricSpace) f g f-uc g-uc)
  ≡ recursiveDyadicIntegral f a b a≤b f-uc Add.+
    recursiveDyadicIntegral g a b a≤b g-uc
recursiveDyadicIntegral-add a b a≤b f g f-uc g-uc =
  recursiveDyadicIntegral-unique
    (λ x → f x Add.+ g x) a b a≤b
    (addIsRadiuswiseUniformlyContinuous
      (snd Real.ℝPremetricSpace) f g f-uc g-uc)
    (recursiveDyadicIntegral f a b a≤b f-uc Add.+
      recursiveDyadicIntegral g a b a≤b g-uc)
    (subst
      (λ sequence → isLimitSequence sequence
        (recursiveDyadicIntegral f a b a≤b f-uc Add.+
          recursiveDyadicIntegral g a b a≤b g-uc))
      (sym (funExt (dyadicRecursiveSum-add f g a b)))
      (addPresIsLimitSequence
        (recursiveDyadicIntegralHasLimit f a b a≤b f-uc)
        (recursiveDyadicIntegralHasLimit g a b a≤b g-uc)))
