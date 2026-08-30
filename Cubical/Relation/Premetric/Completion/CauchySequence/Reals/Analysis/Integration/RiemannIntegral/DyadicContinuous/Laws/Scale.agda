module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicContinuous.Laws.Scale where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base using (_≤ℝ_)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Sequence
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.UniformContinuity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.UniformContinuity.Operations using (scaleIsRadiuswiseUniformlyContinuous)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannSum.DyadicRecursive
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicContinuous.Base

recursiveDyadicIntegral-scale :
  ∀ a b (a≤b : a ≤ℝ b) c f
  (f-uc : IsRadiuswiseUniformlyContinuousℝ f) →
  recursiveDyadicIntegral
    (λ x → c Mul.· f x) a b a≤b
    (scaleIsRadiuswiseUniformlyContinuous
      (snd Real.ℝPremetricSpace) c f f-uc)
  ≡ c Mul.· recursiveDyadicIntegral f a b a≤b f-uc
recursiveDyadicIntegral-scale a b a≤b c f f-uc =
  recursiveDyadicIntegral-unique
    (λ x → c Mul.· f x) a b a≤b
    (scaleIsRadiuswiseUniformlyContinuous
      (snd Real.ℝPremetricSpace) c f f-uc)
    (c Mul.· recursiveDyadicIntegral f a b a≤b f-uc)
    (subst
      (λ sequence → isLimitSequence sequence
        (c Mul.· recursiveDyadicIntegral f a b a≤b f-uc))
      (sym (funExt (dyadicRecursiveSum-scale c f a b)))
      (mulPresIsLimitSequence
        (constantIsLimitSequence c)
        (recursiveDyadicIntegralHasLimit f a b a≤b f-uc)))
