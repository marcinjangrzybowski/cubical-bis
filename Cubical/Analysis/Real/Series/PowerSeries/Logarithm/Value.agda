module Cubical.Analysis.Real.Series.PowerSeries.Logarithm.Value where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Rationals.Base using (fromNatℚ; fromNat)
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Domain.Radius
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Uniform
open import Cubical.Analysis.Real.Series.PowerSeries.Base
open import Cubical.Analysis.Real.Series.PowerSeries.AtZero
open import Cubical.Analysis.Real.Series.PowerSeries.Difference.Derivative
open import Cubical.Analysis.Real.Series.PowerSeries.Logarithm.Coefficients
open import Cubical.Analysis.Real.Series.PowerSeries.Logarithm.Convergence


negativeLogOneMinus : (x : ℝ) → absℝ x <ℝ 1ℝ → ℝ
negativeLogOneMinus x inside =
  powerSeriesValue negativeLogOneMinusCoefficients x
    (negativeLogOneMinusSummable x inside)


negativeLogOneMinusOnClosedRadius : (radius : ℚ₊) → fst radius ℚ.< 1 →
  ClosedAbsRadius (rat (fst radius)) → ℝ
negativeLogOneMinusOnClosedRadius radius radius<1 =
  powerSeriesUniformValueOnClosedRadius negativeLogOneMinusCoefficients
    (rat (fst radius)) (negativeLogOneMinusUniformlyCauchy radius radius<1)


closedSubunitRadiusPointInside : ∀ (radius : ℚ₊) → fst radius ℚ.< 1 →
  (point : ClosedAbsRadius (rat (fst radius))) → absℝ (fst point) <ℝ 1ℝ
closedSubunitRadiusPointInside radius radius<1 point =
  ≤<ℝ-trans (absℝ (fst point)) (rat (fst radius)) 1ℝ (snd point)
    (<ℚ→<ℝ (fst radius) 1 radius<1)


opaque
  negativeLogOneMinusHasSum : ∀ x (inside : absℝ x <ℝ 1ℝ) →
    HasSum (powerSeriesTerms negativeLogOneMinusCoefficients x)
      (negativeLogOneMinus x inside)
  negativeLogOneMinusHasSum x inside =
    seriesSumHasSum (powerSeriesTerms negativeLogOneMinusCoefficients x)
      (negativeLogOneMinusSummable x inside)

  negativeLogOneMinus-independent : ∀ x (first second : absℝ x <ℝ 1ℝ) →
    negativeLogOneMinus x first ≡ negativeLogOneMinus x second
  negativeLogOneMinus-independent x first second =
    seriesSumIndependent (powerSeriesTerms negativeLogOneMinusCoefficients x)
      (negativeLogOneMinusSummable x first)
      (negativeLogOneMinusSummable x second)

  negativeLogOneMinus-zero : ∀ (inside : absℝ 0ℝ <ℝ 1ℝ) →
    negativeLogOneMinus 0ℝ inside ≡ 0ℝ
  negativeLogOneMinus-zero inside =
    powerSeriesValueAtZero negativeLogOneMinusCoefficients
      (negativeLogOneMinusSummable 0ℝ inside)
    ∙ negativeLogOneMinusCoefficient-zero

  negativeLogOneMinusOnClosedRadius-agrees : ∀ (radius : ℚ₊) →
    (radius<1 : fst radius ℚ.< 1) →
    (point : ClosedAbsRadius (rat (fst radius))) →
    (inside : absℝ (fst point) <ℝ 1ℝ) →
    negativeLogOneMinus (fst point) inside ≡
    negativeLogOneMinusOnClosedRadius radius radius<1 point
  negativeLogOneMinusOnClosedRadius-agrees radius radius<1 point inside =
    seriesSumIndependent
      (powerSeriesTerms negativeLogOneMinusCoefficients (fst point))
      (negativeLogOneMinusSummable (fst point) inside)
      (uniformlyCauchySeriesSummableAt
        (negativeLogOneMinusUniformlyCauchy radius radius<1) point)
