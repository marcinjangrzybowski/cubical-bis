module Cubical.Analysis.Real.Series.PowerSeries.Geometric where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Rationals.Base as ℚ

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Inverse.Positive
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Geometric.Base
open import Cubical.Analysis.Real.Series.Geometric.BoundedReal
open import Cubical.Analysis.Real.Series.PowerSeries.Base


-- The geometric series is the power series with every coefficient equal to
-- one.  Naming the coefficients makes subsequent transports state the power
-- series side explicitly.
geometricCoefficients : RealSequence
geometricCoefficients _ = 1ℝ


powerSeriesTerms-geometric-pointwise : ∀ x n →
  powerSeriesTerms geometricCoefficients x n
    ≡ geometricTerms x n
powerSeriesTerms-geometric-pointwise x n =
  mulIdL (geometricTerms x n)


powerSeriesTerms-geometric : ∀ x →
  powerSeriesTerms geometricCoefficients x
    ≡ geometricTerms x
powerSeriesTerms-geometric x =
  funExt (powerSeriesTerms-geometric-pointwise x)


geometricPowerSeriesIsCauchyByRationalBound : ∀ x r →
  RationalContractionBound x r →
  IsCauchySeries (powerSeriesTerms geometricCoefficients x)
geometricPowerSeriesIsCauchyByRationalBound x r bound =
  subst IsCauchySeries
    (sym (powerSeriesTerms-geometric x))
    (realGeometricSeriesIsCauchyByRationalBound x r bound)


geometricPowerSeriesSummableByRationalBound : ∀ x r →
  RationalContractionBound x r →
  PowerSeriesSummableAt geometricCoefficients x
geometricPowerSeriesSummableByRationalBound x r bound =
  subst Summable
    (sym (powerSeriesTerms-geometric x))
    (realGeometricSeriesSummableByRationalBound x r bound)


geometricPowerSeriesHasSumByRationalBound : ∀ x r →
  (bound : RationalContractionBound x r) →
  HasSum (powerSeriesTerms geometricCoefficients x)
    (positiveReciprocal (1ℝ - x)
      (realGeometricPositiveDenominatorByRationalBound
        x r bound))
geometricPowerSeriesHasSumByRationalBound x r bound =
  subst
    (λ terms → HasSum terms
      (positiveReciprocal (1ℝ - x)
        (realGeometricPositiveDenominatorByRationalBound
          x r bound)))
    (sym (powerSeriesTerms-geometric x))
    (realGeometricSeriesHasSumByRationalBound x r bound)


powerSeriesValue-geometricByRationalBound : ∀ x r →
  (bound : RationalContractionBound x r) →
  (summable : PowerSeriesSummableAt geometricCoefficients x) →
  powerSeriesValue geometricCoefficients x summable
    ≡
  positiveReciprocal (1ℝ - x)
    (realGeometricPositiveDenominatorByRationalBound
      x r bound)
powerSeriesValue-geometricByRationalBound x r bound summable =
  seriesSumIndependent
    (powerSeriesTerms geometricCoefficients x)
    summable
    ( positiveReciprocal (1ℝ - x)
        (realGeometricPositiveDenominatorByRationalBound
          x r bound)
    , geometricPowerSeriesHasSumByRationalBound x r bound
    )
