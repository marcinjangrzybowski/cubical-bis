module Cubical.Analysis.Real.Series.PowerSeries.Logarithm.DerivativeConvergence where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Rationals.Base using (fromNatℚ; fromNat)
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Geometric.StrictRational
open import Cubical.Analysis.Real.Series.PowerSeries.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Convergence
open import Cubical.Analysis.Real.Series.PowerSeries.Majorant
open import Cubical.Analysis.Real.Series.PowerSeries.Geometric
open import Cubical.Analysis.Real.Series.PowerSeries.Difference.Uniform
open import Cubical.Analysis.Real.Series.PowerSeries.Difference.Derivative
open import Cubical.Analysis.Real.Series.PowerSeries.Logarithm.Coefficients


opaque
  negativeLogOneMinusDerivativeMajorantIsCauchy : ∀ (radius : ℚ₊) →
    fst radius ℚ.< 1 →
    IsCauchySeries
      (powerSeriesTerms
        (formalDerivativeMajorant negativeLogOneMinusCoefficients)
        (rat (fst radius)))
  negativeLogOneMinusDerivativeMajorantIsCauchy radius radius<1 =
    subst IsCauchySeries
      (sym (cong (λ coefficients → powerSeriesTerms coefficients (rat (fst radius)))
        formalDerivative-negativeLogOneMinus
        ∙ powerSeriesTerms-geometric (rat (fst radius))))
      (strictSignedRationalGeometricSeriesIsCauchy (fst radius)
        (positiveRadiusAbsLessThanOne radius radius<1))


  negativeLogOneMinusFormalDerivativeUniformlyCauchy : ∀ (radius : ℚ₊) →
    fst radius ℚ.< 1 →
    FormalDerivativePowerSeriesUniformlyCauchyOnRadius
      negativeLogOneMinusCoefficients (rat (fst radius))
  negativeLogOneMinusFormalDerivativeUniformlyCauchy radius radius<1 =
    formalDerivativePowerSeriesUniformlyCauchyByCoefficientMajorant
      negativeLogOneMinusCoefficients negativeLogOneMinusCoefficients
      (rat (fst radius)) negativeLogOneMinusSelfMajorized
      (negativeLogOneMinusDerivativeMajorantIsCauchy radius radius<1)


  negativeLogOneMinusDifferenceFactorUniformlyCauchy : ∀ (radius : ℚ₊) →
    fst radius ℚ.< 1 →
    PowerSeriesDifferenceFactorUniformlyCauchyOnRadius
      negativeLogOneMinusCoefficients (rat (fst radius))
  negativeLogOneMinusDifferenceFactorUniformlyCauchy radius radius<1 =
    powerSeriesDifferenceFactorUniformlyCauchyByDerivativeMajorant
      negativeLogOneMinusCoefficients negativeLogOneMinusCoefficients
      (rat (fst radius)) negativeLogOneMinusSelfMajorized
      (negativeLogOneMinusDerivativeMajorantIsCauchy radius radius<1)
