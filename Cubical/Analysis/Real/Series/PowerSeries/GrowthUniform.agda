module Cubical.Analysis.Real.Series.PowerSeries.GrowthUniform where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Order as ℚ

open import Cubical.Relation.Premetric.Mappings

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Domain.Radius
open import Cubical.Analysis.Real.Series.Uniform
open import Cubical.Analysis.Real.Series.PowerSeries.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Convergence
open import Cubical.Analysis.Real.Series.PowerSeries.Growth
open import Cubical.Analysis.Real.Series.PowerSeries.Uniform


powerSeriesUniformlyCauchyByGrowth :
  ∀ bound growth radius coefficients →
  CoefficientGrowthBound bound growth coefficients →
  fst (growthRadius growth radius) ℚ.< 1 →
  UniformlyCauchySeries
    (ClosedRationalRadius radius)
    (powerSeriesOnClosedRadius coefficients radius)
powerSeriesUniformlyCauchyByGrowth
    bound growth radius coefficients
    coefficients-bounded combined<1 =
  uniformlyDominatedSeriesIsUniformlyCauchy
    (powerSeriesOnClosedRadius coefficients radius)
    (coefficientGrowthMajorant bound growth radius)
    (λ point →
      powerSeriesTermAbsBoundByGrowth
        bound growth radius coefficients (fst point)
        coefficients-bounded (snd point))
    (coefficientGeometricMajorantIsCauchyByStrictRadius
      bound (growthRadius growth radius) combined<1)


powerSeriesClosedRadiusSummableByGrowth :
  ∀ bound growth radius coefficients →
  (coefficients-bounded :
    CoefficientGrowthBound bound growth coefficients) →
  (combined<1 : fst (growthRadius growth radius) ℚ.< 1) →
  ∀ point → PowerSeriesSummableAt coefficients (fst point)
powerSeriesClosedRadiusSummableByGrowth
    bound growth radius coefficients
    coefficients-bounded combined<1 point =
  uniformlyCauchySeriesSummableAt
    (powerSeriesUniformlyCauchyByGrowth
      bound growth radius coefficients
      coefficients-bounded combined<1)
    point


powerSeriesClosedRadiusValueByGrowth :
  ∀ bound growth radius coefficients →
  CoefficientGrowthBound bound growth coefficients →
  fst (growthRadius growth radius) ℚ.< 1 →
  ClosedRationalRadius radius → ℝ
powerSeriesClosedRadiusValueByGrowth
    bound growth radius coefficients
    coefficients-bounded combined<1 =
  uniformSeriesValue
    (powerSeriesOnClosedRadius coefficients radius)
    (powerSeriesUniformlyCauchyByGrowth
      bound growth radius coefficients
      coefficients-bounded combined<1)


powerSeriesClosedRadiusValueByGrowthIsContinuous :
  ∀ bound growth radius coefficients →
  (coefficients-bounded :
    CoefficientGrowthBound bound growth coefficients) →
  (combined<1 : fst (growthRadius growth radius) ℚ.< 1) →
  isContinuous
    (ClosedAbsRadiusPremetricSpace (rat (fst radius)) .snd)
    (powerSeriesClosedRadiusValueByGrowth
      bound growth radius coefficients
      coefficients-bounded combined<1)
    (ℝPremetricSpace .snd)
powerSeriesClosedRadiusValueByGrowthIsContinuous
    bound growth radius coefficients
    coefficients-bounded combined<1 =
  uniformSeriesValueIsContinuous
    (ClosedAbsRadiusPremetricSpace (rat (fst radius)) .snd)
    (powerSeriesOnClosedRadius coefficients radius)
    (powerSeriesUniformlyCauchyByGrowth
      bound growth radius coefficients
      coefficients-bounded combined<1)
    (powerSeriesTermOnClosedRadiusIsContinuous coefficients radius)
