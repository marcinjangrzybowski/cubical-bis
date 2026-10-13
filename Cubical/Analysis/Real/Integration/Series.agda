module Cubical.Analysis.Real.Integration.Series where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Uniform
open import Cubical.Analysis.Real.Series.Uniform.Limit
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Base
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Laws.Constant
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Laws.Add
open import Cubical.Analysis.Real.Integration.RiemannIntegral.UniformLimit

private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)

opaque
  partialSumHasRiemannIntegral : ∀ (terms : ℝ → RealSequence) a b values →
    (∀ n → HasRiemannIntegralOn (λ x → terms x n) a b (values n)) →
    ∀ n → HasRiemannIntegralOn (λ x → partialSum (terms x) n) a b (partialSum values n)
  partialSumHasRiemannIntegral terms a b values hasValues zero =
    subst (HasRiemannIntegralOn (λ _ → 0ℝ) a b)
      (ℝRing.0RightAnnihilates (b - a)) (constantHasRiemannIntegral a b 0ℝ)
  partialSumHasRiemannIntegral terms a b values hasValues (suc n) =
    addHasRiemannIntegral (λ x → partialSum (terms x) n) (λ x → terms x n)
      (partialSum values n) (values n)
      (partialSumHasRiemannIntegral terms a b values hasValues n) (hasValues n)

  termwiseIntegralOfUniformSum : ∀ (terms : ℝ → RealSequence) f a b values value →
    (∀ n → HasRiemannIntegralOn (λ x → terms x n) a b (values n)) →
    UniformHasSum (λ (x : ClosedInterval a b) → terms (fst x)) (f ∘ fst) →
    HasSum values value → HasRiemannIntegralOn f a b value
  termwiseIntegralOfUniformSum terms f a b values value hasValues uniform values→value =
    uniformLimitPreservesIntegral (λ n x → partialSum (terms x) n) f a b (partialSum values) value
      (partialSumHasRiemannIntegral terms a b values hasValues)
      (λ ε → PT.map (λ { (N , close) → N , λ n large point → close point n large }) (uniform ε))
      values→value

  integralOfUniformSeries : ∀ (terms : ℝ → RealSequence) f a b → a ≤ℝ b → ∀ values value →
    (∀ n → HasRiemannIntegralOn (λ x → terms x n) a b (values n)) →
    HasRiemannIntegralOn f a b value →
    UniformHasSum (λ (x : ClosedInterval a b) → terms (fst x)) (f ∘ fst) → HasSum values value
  integralOfUniformSeries terms f a b a≤b values value hasValues hasValue uniform =
    integralsConvergeUnderUniformLimit (λ n x → partialSum (terms x) n) f a b a≤b (partialSum values) value
      (partialSumHasRiemannIntegral terms a b values hasValues) hasValue
      (λ ε → PT.map
        (λ { (N , close) → N , λ n large point → close point n large }) (uniform ε))

  uniformlyCauchySeriesSumIsIntegrable : ∀ (terms : ℝ → RealSequence) f a b → a ≤ℝ b →
    (∀ n → IsRiemannIntegrableOn (λ x → terms x n) a b) →
    UniformlyCauchySeries (ClosedInterval a b) (terms ∘ fst) →
    UniformHasSum (λ (x : ClosedInterval a b) → terms (fst x)) (f ∘ fst) → IsRiemannIntegrableOn f a b
  uniformlyCauchySeriesSumIsIntegrable terms f a b a≤b integrable native uniform =
    uniformLimitIsRiemannIntegrableOn (λ n x → partialSum (terms x) n) f a b a≤b
      (λ n → partialSum (λ k → fst (integrable k)) n
        , partialSumHasRiemannIntegral terms a b (λ k → fst (integrable k)) (λ k → snd (integrable k)) n)
      (uniformlyCauchySeriesUniformLimitWitness (terms ∘ fst) (f ∘ fst) native uniform)

  integrateUniformlyCauchySeries : ∀ (terms : ℝ → RealSequence) f a b → a ≤ℝ b →
    (integrable : ∀ n → IsRiemannIntegrableOn (λ x → terms x n) a b) →
    UniformlyCauchySeries (ClosedInterval a b) (terms ∘ fst) →
    UniformHasSum (λ (x : ClosedInterval a b) → terms (fst x)) (f ∘ fst) →
    Σ[ value ∈ ℝ ] HasRiemannIntegralOn f a b value × HasSum (λ n → fst (integrable n)) value
  integrateUniformlyCauchySeries terms f a b a≤b integrable native uniform =
    fst result , snd result
      , integralOfUniformSeries terms f a b a≤b (λ n → fst (integrable n)) (fst result)
        (λ n → snd (integrable n)) (snd result) uniform
    where
    result : IsRiemannIntegrableOn f a b
    result = uniformlyCauchySeriesSumIsIntegrable terms f a b a≤b integrable native uniform
