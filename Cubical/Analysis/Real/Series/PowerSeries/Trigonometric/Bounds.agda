module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Bounds where

open import Cubical.Foundations.Prelude

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Series.Comparison
open import Cubical.Analysis.Real.Series.PowerSeries.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Majorant
open import Cubical.Analysis.Real.Series.PowerSeries.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Exponential.Coefficients
open import
  Cubical.Analysis.Real.Series.PowerSeries.Exponential.Archimedean
open import
  Cubical.Analysis.Real.Series.PowerSeries.Exponential.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Coefficients
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Convergence
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire


sinℝ-absBoundByExponential : ∀ x →
  absℝ (sinℝ x) ≤ℝ exponentialEntireValue (absℝ x)
sinℝ-absBoundByExponential x =
  seriesSumAbsBoundBy
    (powerSeriesTerms sineCoefficients x)
    (powerSeriesTerms exponentialCoefficients (absℝ x))
    (entirePowerSeriesSummableAt
      sineCoefficients sinePowerSeriesEntireUniformlyCauchy x)
    (entirePowerSeriesSummableAt
      exponentialCoefficients
      exponentialPowerSeriesEntireUniformlyCauchy (absℝ x))
    (powerSeriesTermAbsBoundByCoefficientMajorant
      sineCoefficients exponentialCoefficients x (absℝ x)
      sineCoefficientsMajorizedByExponential
      (≤ℝ-refl (absℝ x)))


cosℝ-absBoundByExponential : ∀ x →
  absℝ (cosℝ x) ≤ℝ exponentialEntireValue (absℝ x)
cosℝ-absBoundByExponential x =
  seriesSumAbsBoundBy
    (powerSeriesTerms cosineCoefficients x)
    (powerSeriesTerms exponentialCoefficients (absℝ x))
    (entirePowerSeriesSummableAt
      cosineCoefficients cosinePowerSeriesEntireUniformlyCauchy x)
    (entirePowerSeriesSummableAt
      exponentialCoefficients
      exponentialPowerSeriesEntireUniformlyCauchy (absℝ x))
    (powerSeriesTermAbsBoundByCoefficientMajorant
      cosineCoefficients exponentialCoefficients x (absℝ x)
      cosineCoefficientsMajorizedByExponential
      (≤ℝ-refl (absℝ x)))
