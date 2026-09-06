module Cubical.Analysis.Real.Series.PowerSeries.Logarithm.Convergence where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Rationals.Base using (fromNatℚ; fromNat)
open import Cubical.Data.Sigma
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Order.Strict.Density
open import Cubical.Analysis.Real.Domain.Radius
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Absolute
open import Cubical.Analysis.Real.Series.PowerSeries.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Convergence
open import Cubical.Analysis.Real.Series.PowerSeries.Uniform
open import Cubical.Analysis.Real.Series.PowerSeries.Difference.Derivative
open import Cubical.Analysis.Real.Series.PowerSeries.Logarithm.Coefficients


opaque
  negativeLogOneMinusUniformlyCauchy : ∀ (radius : ℚ₊) →
    fst radius ℚ.< 1 →
    PowerSeriesUniformlyCauchyOnRadius
      negativeLogOneMinusCoefficients (rat (fst radius))
  negativeLogOneMinusUniformlyCauchy radius radius<1 =
    powerSeriesUniformlyCauchyByStrictMajorant
      negativeLogCoefficientBound radius negativeLogOneMinusCoefficients
      negativeLogOneMinusCoefficientsBounded radius<1


  negativeLogOneMinusAbsolutelyCauchyOnRadius : ∀ (radius : ℚ₊) →
    fst radius ℚ.< 1 → ∀ x → absℝ x ≤ℝ rat (fst radius) →
    IsAbsolutelyCauchySeries
      (powerSeriesTerms negativeLogOneMinusCoefficients x)
  negativeLogOneMinusAbsolutelyCauchyOnRadius radius radius<1 x bounded =
    powerSeriesIsAbsolutelyCauchyByStrictMajorant
      negativeLogCoefficientBound radius negativeLogOneMinusCoefficients x
      negativeLogOneMinusCoefficientsBounded bounded radius<1


  -- Rational density is eliminated into a proposition, not used to choose
  -- a radius simultaneously for all points.
  negativeLogOneMinusAbsolutelyCauchy : ∀ x → absℝ x <ℝ 1ℝ →
    IsAbsolutelyCauchySeries
      (powerSeriesTerms negativeLogOneMinusCoefficients x)
  negativeLogOneMinusAbsolutelyCauchy x inside =
    PT.rec squash₁
      (λ { (radius , x<radius , radius<1) →
        negativeLogOneMinusAbsolutelyCauchyOnRadius
          (radius , <ℝ→<ℚ 0 radius
            (≤<ℝ-trans 0ℝ (absℝ x) (rat radius)
              (absNonnegative x) x<radius))
          (<ℝ→<ℚ radius 1 radius<1) x
          (<ℝ-weaken (absℝ x) (rat radius) x<radius) })
      (denseℚinℝ (absℝ x) 1ℝ inside)


  negativeLogOneMinusSummable : ∀ x → absℝ x <ℝ 1ℝ →
    PowerSeriesSummableAt negativeLogOneMinusCoefficients x
  negativeLogOneMinusSummable x inside =
    absoluteCauchySeriesIsSummable
      (powerSeriesTerms negativeLogOneMinusCoefficients x)
      (negativeLogOneMinusAbsolutelyCauchy x inside)
