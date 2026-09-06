module Cubical.Analysis.Real.Series.PowerSeries.Logarithm.Derivative where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Rationals.Base using (fromNatℚ; fromNat)
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.Inverse.Positive
open import Cubical.Analysis.Real.Domain.Radius
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Uniform
open import Cubical.Analysis.Real.Series.Geometric.BoundedReal
open import Cubical.Analysis.Real.Series.PowerSeries.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Convergence
open import Cubical.Analysis.Real.Series.PowerSeries.Derivative
open import Cubical.Analysis.Real.Series.PowerSeries.Geometric
open import Cubical.Analysis.Real.Series.PowerSeries.Difference.Derivative
open import Cubical.Analysis.Real.Series.PowerSeries.Logarithm.Coefficients
open import Cubical.Analysis.Real.Series.PowerSeries.Logarithm.Convergence
open import Cubical.Analysis.Real.Series.PowerSeries.Logarithm.Value
open import Cubical.Analysis.Real.Series.PowerSeries.Logarithm.DerivativeConvergence
open import Cubical.Analysis.Real.Calculus.Derivative.Base


negativeLogOneMinusRadiusBound : ∀ (radius : ℚ₊) → fst radius ℚ.< 1 →
  (point : ClosedAbsRadius (rat (fst radius))) →
  RationalContractionBound (fst point) (fst radius)
negativeLogOneMinusRadiusBound radius radius<1 point =
  snd point , positiveRadiusAbsLessThanOne radius radius<1


negativeLogOneMinusFormalDerivativeOnClosedRadius :
  (radius : ℚ₊) → fst radius ℚ.< 1 →
  ClosedAbsRadius (rat (fst radius)) → ℝ
negativeLogOneMinusFormalDerivativeOnClosedRadius radius radius<1 =
  formalDerivativePowerSeriesUniformValueOnClosedRadius
    negativeLogOneMinusCoefficients (rat (fst radius))
    (negativeLogOneMinusFormalDerivativeUniformlyCauchy radius radius<1)


negativeLogOneMinusReciprocalOnClosedRadius :
  (radius : ℚ₊) → fst radius ℚ.< 1 →
  ClosedAbsRadius (rat (fst radius)) → ℝ
negativeLogOneMinusReciprocalOnClosedRadius radius radius<1 point =
  positiveReciprocal (1ℝ - fst point)
    (realGeometricPositiveDenominatorByRationalBound (fst point) (fst radius)
      (negativeLogOneMinusRadiusBound radius radius<1 point))


opaque
  negativeLogOneMinusFormalDerivativeValue≡Reciprocal :
    ∀ (radius : ℚ₊) (radius<1 : fst radius ℚ.< 1) point →
    negativeLogOneMinusFormalDerivativeOnClosedRadius radius radius<1 point ≡
    negativeLogOneMinusReciprocalOnClosedRadius radius radius<1 point
  negativeLogOneMinusFormalDerivativeValue≡Reciprocal radius radius<1 point =
    seriesSumIndependent derivative-terms
      (uniformlyCauchySeriesSummableAt
        (negativeLogOneMinusFormalDerivativeUniformlyCauchy radius radius<1) point)
      (negativeLogOneMinusReciprocalOnClosedRadius radius radius<1 point
        , subst (λ terms → HasSum terms
            (negativeLogOneMinusReciprocalOnClosedRadius radius radius<1 point))
          (sym (cong (λ coefficients → powerSeriesTerms coefficients (fst point))
            formalDerivative-negativeLogOneMinus))
          (geometricPowerSeriesHasSumByRationalBound (fst point) (fst radius)
            (negativeLogOneMinusRadiusBound radius radius<1 point)))
    where
    derivative-terms : RealSequence
    derivative-terms =
      powerSeriesTerms (formalDerivative negativeLogOneMinusCoefficients) (fst point)


  negativeLogOneMinusHasFormalDerivativeOnClosedRadius :
    ∀ (radius : ℚ₊) (radius<1 : fst radius ℚ.< 1) →
    IsDerivativeAlong (ClosedAbsRadiusPremetricSpace (rat (fst radius)) .snd) fst
      (negativeLogOneMinusOnClosedRadius radius radius<1)
      (negativeLogOneMinusFormalDerivativeOnClosedRadius radius radius<1)
  negativeLogOneMinusHasFormalDerivativeOnClosedRadius radius radius<1 =
    powerSeriesUniformValueHasFormalDerivativeOnClosedRadius
      negativeLogOneMinusCoefficients (rat (fst radius))
      (negativeLogOneMinusUniformlyCauchy radius radius<1)
      (negativeLogOneMinusFormalDerivativeUniformlyCauchy radius radius<1)
      (negativeLogOneMinusDifferenceFactorUniformlyCauchy radius radius<1)


  negativeLogOneMinusHasReciprocalDerivativeOnClosedRadius :
    ∀ (radius : ℚ₊) (radius<1 : fst radius ℚ.< 1) →
    IsDerivativeAlong (ClosedAbsRadiusPremetricSpace (rat (fst radius)) .snd) fst
      (negativeLogOneMinusOnClosedRadius radius radius<1)
      (negativeLogOneMinusReciprocalOnClosedRadius radius radius<1)
  negativeLogOneMinusHasReciprocalDerivativeOnClosedRadius radius radius<1 =
    subst (IsDerivativeAlong
      (ClosedAbsRadiusPremetricSpace (rat (fst radius)) .snd) fst
      (negativeLogOneMinusOnClosedRadius radius radius<1))
      (funExt (negativeLogOneMinusFormalDerivativeValue≡Reciprocal radius radius<1))
      (negativeLogOneMinusHasFormalDerivativeOnClosedRadius radius radius<1)
