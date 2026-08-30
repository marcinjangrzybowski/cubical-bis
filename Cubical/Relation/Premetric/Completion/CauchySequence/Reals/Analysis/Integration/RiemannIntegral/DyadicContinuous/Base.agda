module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannIntegral.DyadicContinuous.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base using (_≤ℝ_)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Sequence
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.UniformContinuity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.RiemannSum.DyadicRecursive


HasRecursiveDyadicIntegral :
  (Real.ℝ → Real.ℝ) → Real.ℝ → Real.ℝ → Real.ℝ → Type₀
HasRecursiveDyadicIntegral f a b value =
  isLimitSequence (dyadicRecursiveSum f a b) value

isPropHasRecursiveDyadicIntegral : ∀ f a b value →
  isProp (HasRecursiveDyadicIntegral f a b value)
isPropHasRecursiveDyadicIntegral f a b value =
  isPropIsLimitSequence (dyadicRecursiveSum f a b) value

RecursiveDyadicIntegralWitness :
  (Real.ℝ → Real.ℝ) → Real.ℝ → Real.ℝ → Type₀
RecursiveDyadicIntegralWitness f a b =
  Σ[ value ∈ Real.ℝ ] HasRecursiveDyadicIntegral f a b value

isPropRecursiveDyadicIntegralWitness : ∀ f a b →
  isProp (RecursiveDyadicIntegralWitness f a b)
isPropRecursiveDyadicIntegralWitness f a b =
  isPropSequenceLimit (dyadicRecursiveSum f a b)

recursiveDyadicIntegralCauchy :
  ∀ f a b → a ≤ℝ b →
  IsRadiuswiseUniformlyContinuousℝ f →
  IsCauchySequence (dyadicRecursiveSum f a b)
recursiveDyadicIntegralCauchy = radiuswiseUCDyadicRecursiveSumIsCauchy

recursiveDyadicIntegral :
  ∀ f a b → a ≤ℝ b →
  IsRadiuswiseUniformlyContinuousℝ f → Real.ℝ
recursiveDyadicIntegral f a b a≤b f-uc =
  limitOfCauchySequence
    (dyadicRecursiveSum f a b)
    (recursiveDyadicIntegralCauchy f a b a≤b f-uc)

recursiveDyadicIntegralHasLimit :
  ∀ f a b (a≤b : a ≤ℝ b) f-uc →
  HasRecursiveDyadicIntegral f a b
    (recursiveDyadicIntegral f a b a≤b f-uc)
recursiveDyadicIntegralHasLimit f a b a≤b f-uc =
  limitOfCauchySequenceIsLimit
    (dyadicRecursiveSum f a b)
    (recursiveDyadicIntegralCauchy f a b a≤b f-uc)

recursiveDyadicIntegralWitness :
  ∀ f a b (a≤b : a ≤ℝ b) f-uc →
  RecursiveDyadicIntegralWitness f a b
recursiveDyadicIntegralWitness f a b a≤b f-uc =
  recursiveDyadicIntegral f a b a≤b f-uc
  , recursiveDyadicIntegralHasLimit f a b a≤b f-uc

recursiveDyadicIntegral-independent :
  ∀ f a b (a≤b a≤b' : a ≤ℝ b)
  (f-uc f-uc' : IsRadiuswiseUniformlyContinuousℝ f) →
  recursiveDyadicIntegral f a b a≤b f-uc ≡
  recursiveDyadicIntegral f a b a≤b' f-uc'
recursiveDyadicIntegral-independent f a b a≤b a≤b' f-uc f-uc' =
  limitOfCauchySequenceIndependent
    (dyadicRecursiveSum f a b)
    (recursiveDyadicIntegralCauchy f a b a≤b f-uc)
    (recursiveDyadicIntegralCauchy f a b a≤b' f-uc')

recursiveDyadicIntegral-unique :
  ∀ f a b (a≤b : a ≤ℝ b) f-uc value →
  HasRecursiveDyadicIntegral f a b value →
  recursiveDyadicIntegral f a b a≤b f-uc ≡ value
recursiveDyadicIntegral-unique f a b a≤b f-uc value has-limit =
  canonicalLimit≡
    (dyadicRecursiveSum f a b)
    (recursiveDyadicIntegralCauchy f a b a≤b f-uc)
    value has-limit
