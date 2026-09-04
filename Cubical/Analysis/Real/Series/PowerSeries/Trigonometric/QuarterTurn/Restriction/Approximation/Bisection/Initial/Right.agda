module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.Bisection.Initial.Right where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
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
  sineQuarterInitialRightImageLower :
    ∀ quarter → IsPositiveQuarterTurn quarter →
    ∀ target → target ≤ℝ 1ℝ →
    ∀ (slack : ℚ₊) →
    target - rat (fst slack) <ℝ sinℝ quarter
  sineQuarterInitialRightImageLower
      quarter positive-quarter target upper slack =
    subst (target - rat (fst slack) <ℝ_)
      (sym (sinℝ-positiveQuarter quarter positive-quarter))
      (<≤ℝ-trans
        (target - rat (fst slack)) target 1ℝ
        (sineQuarter-leftSlack target slack) upper)
