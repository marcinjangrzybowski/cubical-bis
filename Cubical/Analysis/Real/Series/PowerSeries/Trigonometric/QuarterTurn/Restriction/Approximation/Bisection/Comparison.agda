module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.Bisection.Comparison where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Located
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.Bisection.Slack


-- This is the branch selector for finite located bisection.  The alternatives
-- overlap, so no decidable comparison with the target is assumed.

sineQuarterSlackMidpointComparison :
  ∀ (target midpoint : ℝ) (slack : ℚ₊) →
  ∥ (target - rat (fst slack) <ℝ sinℝ midpoint)
    ⊎ (sinℝ midpoint <ℝ target + rat (fst slack)) ∥₁
sineQuarterSlackMidpointComparison target midpoint slack =
  isWeaklyLinear<ℝ
    (target - rat (fst slack))
    (target + rat (fst slack))
    (sinℝ midpoint)
    (sineQuarter-slackBand target slack)
