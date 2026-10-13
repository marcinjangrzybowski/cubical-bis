module Cubical.Analysis.Real.Integration.FundamentalTheorem.Series where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat using (zero; suc)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Uniform
open import Cubical.Analysis.Real.Series.Uniform.Limit
open import Cubical.Analysis.Real.Calculus.Derivative.Basic
open import Cubical.Analysis.Real.Calculus.Derivative.Algebra
open import Cubical.Analysis.Real.Calculus.Derivative.Uniform.Interval
open import Cubical.Analysis.Real.Calculus.MeanValue.Uniform
open import Cubical.Analysis.Real.Integration.FundamentalTheorem.Limits
open import Cubical.Analysis.Real.Integration.FundamentalTheorem.DerivativeLimit

opaque
  partialSumHasUniformDerivativeOn : ∀ (terms derivatives : ℝ → RealSequence) a b →
    (∀ n → IsRadiuswiseUniformDerivativeOn (λ x → terms x n) (λ x → derivatives x n) a b) →
    ∀ n → IsRadiuswiseUniformDerivativeOn
      (λ x → partialSum (terms x) n) (λ x → partialSum (derivatives x) n) a b
  partialSumHasUniformDerivativeOn terms derivatives a b derivative zero =
    uniformDerivativeAlongInterval→on (λ _ → 0ℝ) (λ _ → 0ℝ) a b
      (constantHasUniformDerivativeAlong (ClosedIntervalPremetricSpace a b .snd) fst 0ℝ)
  partialSumHasUniformDerivativeOn terms derivatives a b derivative (suc n) =
    uniformDerivativeAlongInterval→on (λ x → partialSum (terms x) (suc n)) (λ x → partialSum (derivatives x) (suc n)) a b
      (addHasUniformDerivativeAlong (ClosedIntervalPremetricSpace a b .snd) fst
        (λ x → partialSum (terms (fst x)) n) (λ x → terms (fst x) n)
        (λ x → partialSum (derivatives (fst x)) n) (λ x → derivatives (fst x) n)
        (uniformDerivativeOn→alongInterval (λ x → partialSum (terms x) n) (λ x → partialSum (derivatives x) n) a b
          (partialSumHasUniformDerivativeOn terms derivatives a b derivative n))
        (uniformDerivativeOn→alongInterval (λ x → terms x n) (λ x → derivatives x n) a b (derivative n)))

  -- The original series need only converge pointwise when its sum is given.
opaque
  termwiseDerivativeOfPointwiseSum : ∀ (terms derivatives : ℝ → RealSequence) (F f : ℝ → ℝ) (a b : ℝ) →
    (∀ n → IsRadiuswiseUniformDerivativeOn (λ x → terms x n) (λ x → derivatives x n) a b) →
    (∀ (point : ClosedInterval a b) → HasSum (terms (fst point)) (F (fst point))) →
    UniformHasSum (λ (x : ClosedInterval a b) → derivatives (fst x)) (f ∘ fst) →
    IsRadiuswiseUniformDerivativeOn F f a b
  termwiseDerivativeOfPointwiseSum terms derivatives F f a b derivative sum derivativeSum =
    pointwiseLimitPreservesUniformDerivative
      (λ n x → partialSum (terms x) n) (λ n x → partialSum (derivatives x) n) F f a b
      (partialSumHasUniformDerivativeOn terms derivatives a b derivative) sum
      (λ ε → PT.map (λ { (N , close) → N , λ n large point → close point n large }) (derivativeSum ε))

  -- Existing uniform sums can be differentiated with radiuswise data alone.
opaque
  termwiseDerivativeOfUniformSum : ∀ (terms derivatives : ℝ → RealSequence) (F f : ℝ → ℝ) (a b : ℝ) →
    (∀ n → IsRadiuswiseUniformDerivativeOn (λ x → terms x n) (λ x → derivatives x n) a b) →
    UniformHasSum (λ (x : ClosedInterval a b) → terms (fst x)) (F ∘ fst) →
    UniformHasSum (λ (x : ClosedInterval a b) → derivatives (fst x)) (f ∘ fst) →
    IsRadiuswiseUniformDerivativeOn F f a b
  termwiseDerivativeOfUniformSum terms derivatives F f a b derivative sum derivativeSum =
    termwiseDerivativeOfPointwiseSum terms derivatives F f a b derivative (uniformHasSumAt sum) derivativeSum


-- A native uniform Cauchy witness for the derivative series, its identified
-- sum, and convergence of the original series at a construct the sum on
-- the whole interval. Continuity of the derivative sum is not assumed.
module UniformDerivativeSeries (terms derivatives : ℝ → RealSequence) (f : ℝ → ℝ)
    (a b initial : ℝ) (a≤b : a ≤ℝ b)
    (derivative : ∀ n → IsRadiuswiseUniformDerivativeOn (λ x → terms x n) (λ x → derivatives x n) a b)
    (native : UniformlyCauchySeries (ClosedInterval a b) (derivatives ∘ fst))
    (derivativeSum : UniformHasSum (λ (x : ClosedInterval a b) → derivatives (fst x)) (f ∘ fst))
    (initialSum : HasSum (terms a) initial) where
  private
    module L = UniformDerivativeLimit
      (λ n x → partialSum (terms x) n) (λ n x → partialSum (derivatives x) n) f a b initial a≤b
      (partialSumHasUniformDerivativeOn terms derivatives a b derivative)
      (uniformlyCauchySeriesUniformLimitWitness (derivatives ∘ fst) (f ∘ fst) native derivativeSum)
      initialSum

  open L public using (value; hasUniformDerivative; hasDerivative; valueAtLowerEndpoint; uniqueWithInitialValue; limitDerivativeIntegrable)

  opaque
    hasSum : UniformHasSum (λ (x : ClosedInterval a b) → terms (fst x)) (value ∘ fst)
    hasSum ε = PT.map (λ { (N , close) → N , λ point n large → close n large point }) (L.convergesUniformly ε)

  opaque
    hasSumAt : ∀ (point : ClosedInterval a b) → HasSum (terms (fst point)) (value (fst point))
    hasSumAt = uniformHasSumAt hasSum
