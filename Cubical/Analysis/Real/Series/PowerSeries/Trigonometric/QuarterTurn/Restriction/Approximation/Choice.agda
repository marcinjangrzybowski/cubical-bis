module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.Choice where

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
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Characterization
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Reflection
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.Base


-- This is the located-bisection boundary after making countable choice
-- explicit: only bounded source points and convergence of their sine images
-- remain.  The source Cauchy witness is reconstructed below.

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


sineQuarterImageApproximation→approximation :
  ∀ quarter →
  PositiveRationalChoice₀ →
  IsPositiveQuarterTurn quarter →
  IsFirstPositiveCosineZero quarter →
  ∀ target →
  SineQuarterImageApproximation quarter target →
  SineQuarterApproximation quarter target
sineQuarterImageApproximation→approximation
    quarter choice positive-quarter characterization target
    (points , image-limit) =
  points
  , mereChosenSineClosenessReflection-presSeqWitness
      quarter modulus points
      (positiveRationalChoice→convergentSeqWitness choice image-limit)
  , image-limit
  where
  modulus : MereChosenQuarterTurnSineClosenessReflectionModulus quarter
  modulus =
    characterizedQuarterTurn-mereChosenSineClosenessReflectionModulus
      quarter choice positive-quarter characterization


sineQuarterImageApproximateIntermediateValue→approximateIntermediateValue :
  ∀ quarter →
  PositiveRationalChoice₀ →
  IsPositiveQuarterTurn quarter →
  IsFirstPositiveCosineZero quarter →
  SineQuarterImageApproximateIntermediateValue quarter →
  SineQuarterApproximateIntermediateValue quarter
sineQuarterImageApproximateIntermediateValue→approximateIntermediateValue
    quarter choice positive-quarter characterization image-approximation
    target lower upper =
  PT.map
    (sineQuarterImageApproximation→approximation
      quarter choice positive-quarter characterization target)
    (image-approximation target lower upper)
