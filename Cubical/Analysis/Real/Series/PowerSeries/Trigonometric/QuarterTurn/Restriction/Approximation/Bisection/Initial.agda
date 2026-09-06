module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.Bisection.Initial where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Endpoints
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.Bisection.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.Bisection.Initial.Left
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.Bisection.Initial.Right


opaque
  sineQuarterInitialSlackBracket : ∀ quarter →
    IsPositiveQuarterTurn quarter → 0ℝ ≤ℝ quarter →
    ∀ target → (- 1ℝ) ≤ℝ target → target ≤ℝ 1ℝ →
    ∀ slack → SineQuarterSlackBracket quarter target slack
  sineQuarterInitialSlackBracket
      quarter positive-quarter nonnegative target lower upper slack =
    left , right , sineQuarterEndpointsOrdered quarter nonnegative
    , subst (λ value → sinℝ value <ℝ target + rat (fst slack))
        (sym left-value)
        (sineQuarterInitialLeftImageUpper
          quarter positive-quarter target lower slack)
    , subst (λ value → target - rat (fst slack) <ℝ sinℝ value)
        (sym right-value)
        (sineQuarterInitialRightImageLower
          quarter positive-quarter target upper slack)
    where
    left : SineQuarterInterval quarter
    left = sineQuarterLeft quarter nonnegative

    right : SineQuarterInterval quarter
    right = sineQuarterRight quarter nonnegative

    left-value : fst left ≡ - quarter
    left-value = refl

    right-value : fst right ≡ quarter
    right-value = refl
