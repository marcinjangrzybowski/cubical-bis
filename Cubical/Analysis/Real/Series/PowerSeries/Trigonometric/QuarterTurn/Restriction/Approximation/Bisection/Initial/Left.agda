module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.Bisection.Initial.Left where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Endpoints
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.Bisection.Slack


opaque
  sineQuarterInitialLeftImageUpper :
    ∀ quarter → IsPositiveQuarterTurn quarter →
    ∀ target → (- 1ℝ) ≤ℝ target →
    ∀ (slack : ℚ₊) →
    sinℝ (- quarter) <ℝ target + rat (fst slack)
  sineQuarterInitialLeftImageUpper
      quarter positive-quarter target lower slack =
    subst (_<ℝ target + rat (fst slack))
      (sym (sinℝ-negativeQuarter quarter positive-quarter))
      (≤<ℝ-trans
        (- 1ℝ) target (target + rat (fst slack))
        lower (sineQuarter-rightSlack target slack))
