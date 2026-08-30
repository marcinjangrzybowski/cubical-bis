module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicContinuous.Laws.Constant where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base as Mul
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup as Group
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base using (_≤ℝ_)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Sequence
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.UniformContinuity.Operations
  using (constantIsRadiuswiseUniformlyContinuous)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannSum.DyadicRecursive
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicContinuous.Base

recursiveDyadicIntegral-constant : ∀ a b (a≤b : a ≤ℝ b) c →
  recursiveDyadicIntegral (λ _ → c) a b a≤b
    (constantIsRadiuswiseUniformlyContinuous
      (snd Real.ℝPremetricSpace) c)
  ≡ (b Group.- a) Mul.· c
recursiveDyadicIntegral-constant a b a≤b c =
  recursiveDyadicIntegral-unique
    (λ _ → c) a b a≤b
    (constantIsRadiuswiseUniformlyContinuous
      (snd Real.ℝPremetricSpace) c)
    ((b Group.- a) Mul.· c)
    (subst
      (λ sequence → isLimitSequence sequence ((b Group.- a) Mul.· c))
      (sym (funExt (dyadicRecursiveSum-constant a b c)))
      (constantIsLimitSequence ((b Group.- a) Mul.· c)))
