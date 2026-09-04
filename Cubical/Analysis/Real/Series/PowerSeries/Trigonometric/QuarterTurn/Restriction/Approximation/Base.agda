module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁; squash₁)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Sequence
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Base


-- This is the completion-compatible output expected from an approximate
-- bisection construction.  The source points come with one native Cauchy
-- witness, while their sine values converge to the requested target.

SineQuarterApproximation : ℝ → ℝ → Type₀
SineQuarterApproximation quarter target =
  Σ[ points ∈ (ℕ → SineQuarterInterval quarter) ]
    SeqWitness (λ n → fst (points n)) ×
    isLimitSequence (λ n → sinℝ (fst (points n))) target


SineQuarterApproximateIntermediateValue : ℝ → Type₀
SineQuarterApproximateIntermediateValue quarter =
  ∀ target → (- 1ℝ) ≤ℝ target → target ≤ℝ 1ℝ →
    ∥ SineQuarterApproximation quarter target ∥₁


isPropSineQuarterApproximateIntermediateValue : ∀ quarter →
  isProp (SineQuarterApproximateIntermediateValue quarter)
isPropSineQuarterApproximateIntermediateValue quarter =
  isPropΠ3 λ _ _ _ → squash₁
