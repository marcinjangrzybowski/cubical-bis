module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Approximation.Bisection.Geometry where

open import Cubical.Foundations.Prelude

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Geometry


opaque
  sineQuarter-midpoint-lower : ∀ x y → x ≤ℝ y →
    x ≤ℝ quarterTurnMidpoint x y
  sineQuarter-midpoint-lower x y x≤y =
    subst (λ z → z ≤ℝ quarterTurnMidpoint x y)
      (quarterTurnHalfScalar-double x)
      (quarterTurnHalfScalar-pres≤
        {x = x + x} {y = x + y}
        (addPres≤L x y x x≤y))


  sineQuarter-midpoint-upper : ∀ x y → x ≤ℝ y →
    quarterTurnMidpoint x y ≤ℝ y
  sineQuarter-midpoint-upper x y x≤y =
    subst (quarterTurnMidpoint x y ≤ℝ_)
      (quarterTurnHalfScalar-double y)
      (quarterTurnHalfScalar-pres≤
        {x = x + y} {y = y + y}
        (addPres≤R x y y x≤y))
