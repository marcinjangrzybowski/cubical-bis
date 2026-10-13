module Cubical.Analysis.Complex.Series.PowerSeries.Elementary.Convergence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Functions.Powers using (powℝ)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Series.Base using (RealSequence)
open import Cubical.Analysis.Real.Series.PowerSeries.Majorant using (CoefficientMajorizedBy)
import Cubical.Analysis.Real.Series.Base as Real
import Cubical.Analysis.Real.Series.Absolute as Real
import Cubical.Analysis.Real.Series.PowerSeries.Base as Real
import Cubical.Analysis.Real.Series.PowerSeries.Majorant as Real
import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Coefficients as Real
import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Calculus as Real
import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Archimedean as Real
import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Coefficients as Real
import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Convergence as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Series.Absolute
open import Cubical.Analysis.Complex.Series.PowerSeries.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Bounds
open import Cubical.Analysis.Complex.Series.PowerSeries.Convergence
open import Cubical.Analysis.Complex.Series.PowerSeries.RealEmbedding
open import Cubical.Analysis.Complex.Series.PowerSeries.Elementary.Coefficients

-- Transfer the real factorial comparison once for every embedded real
-- coefficient family dominated by 1/n!. All witnesses are native Cauchy data.
opaque
  exponentialDominatedComplexMajorantIsCauchy : ∀ coefficients radius →
    CoefficientMajorizedBy coefficients Real.exponentialCoefficients → 0ℝ ≤ℝ radius →
    Real.IsCauchySeries (complexPowerSeriesMajorant (realCoefficientsℂ coefficients) radius)
  exponentialDominatedComplexMajorantIsCauchy coefficients radius majorized positive =
    subst Real.IsCauchySeries
      (sym (funExt λ n → cong (_· powℝ radius n) (normℂ-fromℝ (coefficients n))))
      (Real.dominatedCauchySeriesIsCauchy
        (Real.powerSeriesTerms (absℝ ∘ coefficients) radius)
        (Real.powerSeriesTerms Real.exponentialCoefficients radius)
        (Real.powerSeriesTermAbsBoundByCoefficientMajorant (absℝ ∘ coefficients) Real.exponentialCoefficients
          radius radius (λ n → subst (_≤ℝ Real.exponentialCoefficients n) (sym (absIdem (coefficients n))) (majorized n))
          (subst (_≤ℝ radius) (sym (absOfNonnegative radius positive)) (≤ℝ-refl radius)))
        (Real.exponentialPowerSeriesIsCauchyEverywhere radius))

exponentialComplexMajorantIsCauchy : ∀ radius → 0ℝ ≤ℝ radius →
  Real.IsCauchySeries (complexPowerSeriesMajorant exponentialCoefficientsℂ radius)
exponentialComplexMajorantIsCauchy radius = exponentialDominatedComplexMajorantIsCauchy
  Real.exponentialCoefficients radius
  (Real.nonnegativeCoefficientsSelfMajorized Real.exponentialCoefficients Real.exponentialCoefficients-nonnegative)

sineComplexMajorantIsCauchy : ∀ radius → 0ℝ ≤ℝ radius →
  Real.IsCauchySeries (complexPowerSeriesMajorant sineCoefficientsℂ radius)
sineComplexMajorantIsCauchy radius = exponentialDominatedComplexMajorantIsCauchy
  Real.sineCoefficients radius Real.sineCoefficientsMajorizedByExponential

cosineComplexMajorantIsCauchy : ∀ radius → 0ℝ ≤ℝ radius →
  Real.IsCauchySeries (complexPowerSeriesMajorant cosineCoefficientsℂ radius)
cosineComplexMajorantIsCauchy radius = exponentialDominatedComplexMajorantIsCauchy
  Real.cosineCoefficients radius Real.cosineCoefficientsMajorizedByExponential

exponentialComplexSeriesIsAbsolutelyCauchy : ∀ z →
  IsComplexAbsolutelyCauchySeries (powerSeriesTermsℂ exponentialCoefficientsℂ z)
exponentialComplexSeriesIsAbsolutelyCauchy z = complexPowerSeriesAbsolutelyCauchyOn
  exponentialCoefficientsℂ (normℂ z) (exponentialComplexMajorantIsCauchy (normℂ z) (normℂ-nonnegative z))
  z (≤ℝ-refl (normℂ z))

sineComplexSeriesIsAbsolutelyCauchy : ∀ z →
  IsComplexAbsolutelyCauchySeries (powerSeriesTermsℂ sineCoefficientsℂ z)
sineComplexSeriesIsAbsolutelyCauchy z = complexPowerSeriesAbsolutelyCauchyOn
  sineCoefficientsℂ (normℂ z) (sineComplexMajorantIsCauchy (normℂ z) (normℂ-nonnegative z)) z (≤ℝ-refl (normℂ z))

cosineComplexSeriesIsAbsolutelyCauchy : ∀ z →
  IsComplexAbsolutelyCauchySeries (powerSeriesTermsℂ cosineCoefficientsℂ z)
cosineComplexSeriesIsAbsolutelyCauchy z = complexPowerSeriesAbsolutelyCauchyOn
  cosineCoefficientsℂ (normℂ z) (cosineComplexMajorantIsCauchy (normℂ z) (normℂ-nonnegative z)) z (≤ℝ-refl (normℂ z))
