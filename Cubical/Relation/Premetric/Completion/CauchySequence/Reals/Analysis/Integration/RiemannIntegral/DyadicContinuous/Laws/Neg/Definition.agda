module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicContinuous.Laws.Neg.Definition where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation as Neg
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base using (_≤ℝ_)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.UniformContinuity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.UniformContinuity.Operations using (negIsRadiuswiseUniformlyContinuous)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicContinuous.Base

negatedFunctionIsRadiuswiseUniformlyContinuous :
  ∀ f → IsRadiuswiseUniformlyContinuousℝ f →
  IsRadiuswiseUniformlyContinuousℝ (Neg.-_ ∘ f)
negatedFunctionIsRadiuswiseUniformlyContinuous f f-uc =
  negIsRadiuswiseUniformlyContinuous
    (snd Real.ℝPremetricSpace) f f-uc

recursiveDyadicIntegralNeg :
  ∀ a b (a≤b : a ≤ℝ b) f →
  IsRadiuswiseUniformlyContinuousℝ f → Real.ℝ
recursiveDyadicIntegralNeg a b a≤b f f-uc =
  recursiveDyadicIntegral (Neg.-_ ∘ f) a b a≤b
    (negatedFunctionIsRadiuswiseUniformlyContinuous f f-uc)
