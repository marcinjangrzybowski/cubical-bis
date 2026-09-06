module Cubical.Analysis.Real.Series.PowerSeries.Logarithm.UniformDerivative where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Rationals.Base using (fromNatℚ; fromNat)
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Domain.Radius
open import Cubical.Analysis.Real.Series.PowerSeries.Difference.UniformDerivative
open import Cubical.Analysis.Real.Series.PowerSeries.Logarithm.Coefficients
open import Cubical.Analysis.Real.Series.PowerSeries.Logarithm.Convergence
open import Cubical.Analysis.Real.Series.PowerSeries.Logarithm.Value
open import Cubical.Analysis.Real.Series.PowerSeries.Logarithm.Derivative
open import Cubical.Analysis.Real.Series.PowerSeries.Logarithm.DerivativeConvergence
open import Cubical.Analysis.Real.Calculus.Derivative.Uniform


-- The logarithm series has a uniform first-order remainder on each closed
-- rational radius below one, without a globally selected continuity modulus.
negativeLogOneMinusHasUniformFormalDerivativeOnClosedRadius :
  ∀ (radius : ℚ₊) (radius<1 : fst radius ℚ.< 1) →
  IsRadiuswiseUniformDerivativeAlong
    (ClosedAbsRadiusPremetricSpace (rat (fst radius)) .snd) fst
    (negativeLogOneMinusOnClosedRadius radius radius<1)
    (negativeLogOneMinusFormalDerivativeOnClosedRadius radius radius<1)
negativeLogOneMinusHasUniformFormalDerivativeOnClosedRadius radius radius<1 =
  powerSeriesUniformValueHasUniformFormalDerivativeOnClosedRadius
    negativeLogOneMinusCoefficients (rat (fst radius))
    (<ℝ-weaken 0ℝ (rat (fst radius)) (<ℚ→<ℝ 0 (fst radius) (snd radius)))
    (negativeLogOneMinusUniformlyCauchy radius radius<1)
    (negativeLogOneMinusFormalDerivativeUniformlyCauchy radius radius<1)
    (negativeLogOneMinusDifferenceFactorUniformlyCauchy radius radius<1)


negativeLogOneMinusHasUniformReciprocalDerivativeOnClosedRadius :
  ∀ (radius : ℚ₊) (radius<1 : fst radius ℚ.< 1) →
  IsRadiuswiseUniformDerivativeAlong
    (ClosedAbsRadiusPremetricSpace (rat (fst radius)) .snd) fst
    (negativeLogOneMinusOnClosedRadius radius radius<1)
    (negativeLogOneMinusReciprocalOnClosedRadius radius radius<1)
negativeLogOneMinusHasUniformReciprocalDerivativeOnClosedRadius radius radius<1 =
  subst
    (IsRadiuswiseUniformDerivativeAlong
      (ClosedAbsRadiusPremetricSpace (rat (fst radius)) .snd) fst
      (negativeLogOneMinusOnClosedRadius radius radius<1))
    (funExt (negativeLogOneMinusFormalDerivativeValue≡Reciprocal radius radius<1))
    (negativeLogOneMinusHasUniformFormalDerivativeOnClosedRadius radius radius<1)
