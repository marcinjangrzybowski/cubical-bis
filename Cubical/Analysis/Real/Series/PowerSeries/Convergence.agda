module Cubical.Analysis.Real.Series.PowerSeries.Convergence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Rationals.Base as ℚ
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Operations
open import Cubical.Analysis.Real.Series.Comparison
open import Cubical.Analysis.Real.Series.Absolute
open import Cubical.Analysis.Real.Series.Geometric
open import Cubical.Analysis.Real.Series.PowerSeries.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Bounds

open PositiveRationals using (ℚ₊)


coefficientGeometricMajorantIsCauchy : ∀ bound radius →
  fst radius ℚ.≤ halfℚ →
  IsCauchySeries
    (coefficientGeometricMajorant bound radius)
coefficientGeometricMajorantIsCauchy bound radius radius≤half =
  rationalScaleSeriesIsCauchy
    (fst bound)
    (geometricTerms (rat (fst radius)))
    (rationalGeometricSeriesIsCauchy
      (fst radius)
      (ℚ.<Weaken≤ 0 (fst radius) (snd radius))
      radius≤half)


coefficientGeometricMajorantSummable : ∀ bound radius →
  fst radius ℚ.≤ halfℚ →
  Summable (coefficientGeometricMajorant bound radius)
coefficientGeometricMajorantSummable bound radius radius≤half =
  scaleSummable
    (rat (fst bound))
    (geometricTerms (rat (fst radius)))
    (rationalGeometricSeriesSummable
      (fst radius)
      (ℚ.<Weaken≤ 0 (fst radius) (snd radius))
      radius≤half)


powerSeriesIsAbsolutelyCauchyByHalfMajorant :
  ∀ bound radius coefficients x →
  CoefficientAbsBound bound coefficients →
  absℝ x ≤ℝ rat (fst radius) →
  fst radius ℚ.≤ halfℚ →
  IsAbsolutelyCauchySeries
    (powerSeriesTerms coefficients x)
powerSeriesIsAbsolutelyCauchyByHalfMajorant
    bound radius coefficients x
    coefficients-bounded absx≤radius radius≤half =
  dominatedCauchySeriesIsCauchy
    (absℝ ∘ powerSeriesTerms coefficients x)
    (coefficientGeometricMajorant bound radius)
    dominates
    (coefficientGeometricMajorantIsCauchy
      bound radius radius≤half)
  where
  dominates : ∀ n →
    absℝ (absℝ (powerSeriesTerms coefficients x n)) ≤ℝ
    coefficientGeometricMajorant bound radius n
  dominates n =
    subst
      (_≤ℝ coefficientGeometricMajorant bound radius n)
      (sym (absIdem (powerSeriesTerms coefficients x n)))
      (powerSeriesTermAbsBound
        bound radius coefficients x
        coefficients-bounded absx≤radius n)


powerSeriesIsCauchyByHalfMajorant :
  ∀ bound radius coefficients x →
  CoefficientAbsBound bound coefficients →
  absℝ x ≤ℝ rat (fst radius) →
  fst radius ℚ.≤ halfℚ →
  IsCauchySeries (powerSeriesTerms coefficients x)
powerSeriesIsCauchyByHalfMajorant
    bound radius coefficients x
    coefficients-bounded absx≤radius radius≤half =
  absoluteCauchySeriesIsCauchy
    (powerSeriesTerms coefficients x)
    (powerSeriesIsAbsolutelyCauchyByHalfMajorant
      bound radius coefficients x
      coefficients-bounded absx≤radius radius≤half)


powerSeriesIsSummableByHalfMajorant :
  ∀ bound radius coefficients x →
  CoefficientAbsBound bound coefficients →
  absℝ x ≤ℝ rat (fst radius) →
  fst radius ℚ.≤ halfℚ →
  PowerSeriesSummableAt coefficients x
powerSeriesIsSummableByHalfMajorant
    bound radius coefficients x
    coefficients-bounded absx≤radius radius≤half =
  absoluteCauchySeriesIsSummable
    (powerSeriesTerms coefficients x)
    (powerSeriesIsAbsolutelyCauchyByHalfMajorant
      bound radius coefficients x
      coefficients-bounded absx≤radius radius≤half)


powerSeriesValueAbsBoundByHalfMajorant :
  ∀ bound radius coefficients x
  (coefficients-bounded : CoefficientAbsBound bound coefficients)
  (absx≤radius : absℝ x ≤ℝ rat (fst radius))
  (radius≤half : fst radius ℚ.≤ halfℚ) →
  absℝ
    (powerSeriesValue coefficients x
      (powerSeriesIsSummableByHalfMajorant
        bound radius coefficients x
        coefficients-bounded absx≤radius radius≤half))
    ≤ℝ
  seriesSum
    (coefficientGeometricMajorant bound radius)
    (coefficientGeometricMajorantSummable
      bound radius radius≤half)
powerSeriesValueAbsBoundByHalfMajorant
    bound radius coefficients x
    coefficients-bounded absx≤radius radius≤half =
  seriesSumAbsBoundBy
    (powerSeriesTerms coefficients x)
    (coefficientGeometricMajorant bound radius)
    (powerSeriesIsSummableByHalfMajorant
      bound radius coefficients x
      coefficients-bounded absx≤radius radius≤half)
    (coefficientGeometricMajorantSummable
      bound radius radius≤half)
    (powerSeriesTermAbsBound
      bound radius coefficients x
      coefficients-bounded absx≤radius)
