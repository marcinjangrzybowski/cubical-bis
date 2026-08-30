module Cubical.Analysis.Real.Series.PowerSeries.Convergence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Rationals.Base as ℚ
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
open import Cubical.Algebra.OrderedCommRing
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


private
  module ℚOrder =
    OrderedCommRingTheory ℚOrderedCommRing


positiveRadiusAbsLessThanOne : ∀ radius →
  fst radius ℚ.< 1 → ℚOrder.abs (fst radius) ℚ.< 1
positiveRadiusAbsLessThanOne radius radius<1 =
  subst (ℚ._< 1)
    (sym
      (ℚOrder.0≤→abs≡id (fst radius)
        (ℚ.<Weaken≤ 0 (fst radius) (snd radius))))
    radius<1


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


coefficientGeometricMajorantIsCauchyByStrictRadius : ∀ bound radius →
  fst radius ℚ.< 1 →
  IsCauchySeries
    (coefficientGeometricMajorant bound radius)
coefficientGeometricMajorantIsCauchyByStrictRadius
    bound radius radius<1 =
  rationalScaleSeriesIsCauchy
    (fst bound)
    (geometricTerms (rat (fst radius)))
    (strictSignedRationalGeometricSeriesIsCauchy
      (fst radius)
      (positiveRadiusAbsLessThanOne radius radius<1))


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


coefficientGeometricMajorantSummableByStrictRadius : ∀ bound radius →
  fst radius ℚ.< 1 →
  Summable (coefficientGeometricMajorant bound radius)
coefficientGeometricMajorantSummableByStrictRadius
    bound radius radius<1 =
  scaleSummable
    (rat (fst bound))
    (geometricTerms (rat (fst radius)))
    (strictSignedRationalGeometricSeriesSummable
      (fst radius)
      (positiveRadiusAbsLessThanOne radius radius<1))


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


powerSeriesIsAbsolutelyCauchyByStrictMajorant :
  ∀ bound radius coefficients x →
  CoefficientAbsBound bound coefficients →
  absℝ x ≤ℝ rat (fst radius) →
  fst radius ℚ.< 1 →
  IsAbsolutelyCauchySeries
    (powerSeriesTerms coefficients x)
powerSeriesIsAbsolutelyCauchyByStrictMajorant
    bound radius coefficients x
    coefficients-bounded absx≤radius radius<1 =
  dominatedCauchySeriesIsCauchy
    (absℝ ∘ powerSeriesTerms coefficients x)
    (coefficientGeometricMajorant bound radius)
    dominates
    (coefficientGeometricMajorantIsCauchyByStrictRadius
      bound radius radius<1)
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


powerSeriesIsCauchyByStrictMajorant :
  ∀ bound radius coefficients x →
  CoefficientAbsBound bound coefficients →
  absℝ x ≤ℝ rat (fst radius) →
  fst radius ℚ.< 1 →
  IsCauchySeries (powerSeriesTerms coefficients x)
powerSeriesIsCauchyByStrictMajorant
    bound radius coefficients x
    coefficients-bounded absx≤radius radius<1 =
  absoluteCauchySeriesIsCauchy
    (powerSeriesTerms coefficients x)
    (powerSeriesIsAbsolutelyCauchyByStrictMajorant
      bound radius coefficients x
      coefficients-bounded absx≤radius radius<1)


powerSeriesIsSummableByStrictMajorant :
  ∀ bound radius coefficients x →
  CoefficientAbsBound bound coefficients →
  absℝ x ≤ℝ rat (fst radius) →
  fst radius ℚ.< 1 →
  PowerSeriesSummableAt coefficients x
powerSeriesIsSummableByStrictMajorant
    bound radius coefficients x
    coefficients-bounded absx≤radius radius<1 =
  absoluteCauchySeriesIsSummable
    (powerSeriesTerms coefficients x)
    (powerSeriesIsAbsolutelyCauchyByStrictMajorant
      bound radius coefficients x
      coefficients-bounded absx≤radius radius<1)


powerSeriesValueAbsBoundByStrictMajorant :
  ∀ bound radius coefficients x
  (coefficients-bounded : CoefficientAbsBound bound coefficients)
  (absx≤radius : absℝ x ≤ℝ rat (fst radius))
  (radius<1 : fst radius ℚ.< 1) →
  absℝ
    (powerSeriesValue coefficients x
      (powerSeriesIsSummableByStrictMajorant
        bound radius coefficients x
        coefficients-bounded absx≤radius radius<1))
    ≤ℝ
  seriesSum
    (coefficientGeometricMajorant bound radius)
    (coefficientGeometricMajorantSummableByStrictRadius
      bound radius radius<1)
powerSeriesValueAbsBoundByStrictMajorant
    bound radius coefficients x
    coefficients-bounded absx≤radius radius<1 =
  seriesSumAbsBoundBy
    (powerSeriesTerms coefficients x)
    (coefficientGeometricMajorant bound radius)
    (powerSeriesIsSummableByStrictMajorant
      bound radius coefficients x
      coefficients-bounded absx≤radius radius<1)
    (coefficientGeometricMajorantSummableByStrictRadius
      bound radius radius<1)
    (powerSeriesTermAbsBound
      bound radius coefficients x
      coefficients-bounded absx≤radius)
