module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.Image where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Sequence
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Base

-- Image convergence alone does not supply a source Cauchy witness.
-- These definitions record only the approximation data actually given.

SineQuarterImageApproximation : ℝ → ℝ → Type₀
SineQuarterImageApproximation quarter target =
  Σ[ points ∈ (ℕ → SineQuarterInterval quarter) ]
    isLimitSequence (λ n → sinℝ (fst (points n))) target


SineQuarterImageApproximateIntermediateValue : ℝ → Type₀
SineQuarterImageApproximateIntermediateValue quarter =
  ∀ target → (- 1ℝ) ≤ℝ target → target ≤ℝ 1ℝ →
    ∥ SineQuarterImageApproximation quarter target ∥₁


isPropSineQuarterImageApproximateIntermediateValue : ∀ quarter →
  isProp (SineQuarterImageApproximateIntermediateValue quarter)
isPropSineQuarterImageApproximateIntermediateValue quarter =
  isPropΠ3 λ _ _ _ → squash₁
