module Cubical.Analysis.Real.Series.PowerSeries.Uniform where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals.Base as ℚ
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Domain.Radius
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Uniform
open import Cubical.Analysis.Real.Series.Geometric.Rational
open import Cubical.Analysis.Real.Series.PowerSeries.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Bounds
open import Cubical.Analysis.Real.Series.PowerSeries.Convergence

open PositiveRationals using (ℚ₊)


ClosedRationalRadius : ℚ₊ → Type₀
ClosedRationalRadius radius =
  ClosedAbsRadius (rat (fst radius))


powerSeriesOnClosedRadius :
  RealSequence → (radius : ℚ₊) →
  ClosedRationalRadius radius → RealSequence
powerSeriesOnClosedRadius coefficients radius point =
  powerSeriesTerms coefficients (fst point)


powerSeriesUniformlyCauchyByHalfMajorant :
  ∀ bound radius coefficients →
  CoefficientAbsBound bound coefficients →
  fst radius ℚ.≤ halfℚ →
  UniformlyCauchySeries
    (ClosedRationalRadius radius)
    (powerSeriesOnClosedRadius coefficients radius)
powerSeriesUniformlyCauchyByHalfMajorant
    bound radius coefficients coefficients-bounded radius≤half =
  uniformlyDominatedSeriesIsUniformlyCauchy
    (powerSeriesOnClosedRadius coefficients radius)
    (coefficientGeometricMajorant bound radius)
    (λ point →
      powerSeriesTermAbsBound
        bound radius coefficients (fst point)
        coefficients-bounded (snd point))
    (coefficientGeometricMajorantIsCauchy
      bound radius radius≤half)


powerSeriesClosedRadiusSummable :
  ∀ bound radius coefficients →
  (coefficients-bounded : CoefficientAbsBound bound coefficients) →
  (radius≤half : fst radius ℚ.≤ halfℚ) →
  ∀ point → PowerSeriesSummableAt coefficients (fst point)
powerSeriesClosedRadiusSummable
    bound radius coefficients coefficients-bounded radius≤half point =
  uniformlyCauchySeriesSummableAt
    (powerSeriesUniformlyCauchyByHalfMajorant
      bound radius coefficients coefficients-bounded radius≤half)
    point


powerSeriesClosedRadiusValue :
  ∀ bound radius coefficients →
  CoefficientAbsBound bound coefficients →
  fst radius ℚ.≤ halfℚ →
  ClosedRationalRadius radius → ℝ
powerSeriesClosedRadiusValue
    bound radius coefficients coefficients-bounded radius≤half =
  uniformSeriesValue
    (powerSeriesOnClosedRadius coefficients radius)
    (powerSeriesUniformlyCauchyByHalfMajorant
      bound radius coefficients coefficients-bounded radius≤half)
