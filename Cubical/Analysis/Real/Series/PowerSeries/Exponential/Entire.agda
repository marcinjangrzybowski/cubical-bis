module Cubical.Analysis.Real.Series.PowerSeries.Exponential.Entire where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.NatPlusOne using (ℕ₊₁→ℕ)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Archimedean
open import Cubical.Analysis.Real.Domain.Radius
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Uniform
open import Cubical.Analysis.Real.Series.PowerSeries.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Difference.Derivative
open import Cubical.Analysis.Real.Series.PowerSeries.Difference.Uniform
open import Cubical.Analysis.Real.Series.PowerSeries.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Entire.HigherDerivative
open import Cubical.Analysis.Real.Series.PowerSeries.RepeatedDerivative
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Coefficients
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Archimedean
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Calculus
open import Cubical.Analysis.Real.Calculus.Derivative.Base


-- The natural-radius divided-difference estimate restricts to an arbitrary
-- real radius in exactly the same way as the term-series estimate.
exponentialDifferenceFactorUniformlyCauchyFromNaturalRealBound :
  ∀ radius n →
  radius <ℝ rat (naturalRational n) →
  PowerSeriesDifferenceFactorUniformlyCauchyOnRadius
    exponentialCoefficients radius
exponentialDifferenceFactorUniformlyCauchyFromNaturalRealBound
    radius n radius<n =
  powerSeriesDifferenceFactorUniformlyCauchyOnSmallerRadius
    exponentialCoefficients radius (rat (naturalRational n))
    (<ℝ-weaken radius (rat (naturalRational n)) radius<n)
    (exponentialDifferenceFactorUniformlyCauchyWithinNaturalBound
      (ℕ₊₁→ℕ n) (naturalBound n)
      (naturalRadiusBelowSuccessorBase n))


opaque
  exponentialPowerSeriesDifferenceFactorEntireUniformlyCauchy :
    EntirePowerSeriesDifferenceFactorUniformlyCauchy
      exponentialCoefficients
  exponentialPowerSeriesDifferenceFactorEntireUniformlyCauchy radius =
    PT.rec
      (isPropUniformlyCauchySeries
        (ClosedAbsRadiusPair radius)
        (powerSeriesDifferenceFactorOnClosedRadius
          exponentialCoefficients radius))
      (λ where
        (n , radius<n) →
          exponentialDifferenceFactorUniformlyCauchyFromNaturalRealBound
            radius n radius<n)
      (∃naturalUpperBound radius)


-- Since every formal derivative of the exponential coefficient sequence is
-- the original sequence, the base entire witnesses package all finite orders.
opaque
  exponentialPowerSeriesEntireRepeatedFormalDerivativesUniformlyCauchy :
    EntireRepeatedFormalDerivativesUniformlyCauchy
      exponentialCoefficients
  exponentialPowerSeriesEntireRepeatedFormalDerivativesUniformlyCauchy
      radius order =
    subst
      (λ coefficients →
        PowerSeriesUniformlyCauchyOnRadius coefficients radius)
      (sym (repeatedFormalDerivative-exponentialCoefficients order))
      (exponentialPowerSeriesEntireUniformlyCauchy radius)

  exponentialPowerSeriesEntireRepeatedDifferenceFactorsUniformlyCauchy :
    EntireRepeatedFormalDerivativeDifferenceFactorsUniformlyCauchy
      exponentialCoefficients
  exponentialPowerSeriesEntireRepeatedDifferenceFactorsUniformlyCauchy
      radius order =
    subst
      (λ coefficients →
        PowerSeriesDifferenceFactorUniformlyCauchyOnRadius
          coefficients radius)
      (sym (repeatedFormalDerivative-exponentialCoefficients order))
      (exponentialPowerSeriesDifferenceFactorEntireUniformlyCauchy radius)


exponentialEntireValue : ℝ → ℝ
exponentialEntireValue =
  entirePowerSeriesValue
    exponentialCoefficients
    exponentialPowerSeriesEntireUniformlyCauchy


exponentialEntireHigherDerivativeValue : ℕ → ℝ → ℝ
exponentialEntireHigherDerivativeValue =
  entireHigherDerivativeValue
    exponentialCoefficients
    exponentialPowerSeriesEntireRepeatedFormalDerivativesUniformlyCauchy


exponentialEntireHigherDerivativeValue-fixedPoint : ∀ order x →
  exponentialEntireHigherDerivativeValue order x
    ≡ exponentialEntireValue x
exponentialEntireHigherDerivativeValue-fixedPoint order x =
  entirePowerSeriesValuePresPath
    (repeatedFormalDerivative order exponentialCoefficients)
    exponentialCoefficients
    (repeatedFormalDerivative-exponentialCoefficients order)
    (entireRepeatedFormalDerivativeUniform
      exponentialCoefficients
      exponentialPowerSeriesEntireRepeatedFormalDerivativesUniformlyCauchy
      order)
    exponentialPowerSeriesEntireUniformlyCauchy x


exponentialEntireHigherDerivativeLocalSuccessorValue :
  ℕ → ℝ → ℝ
exponentialEntireHigherDerivativeLocalSuccessorValue order x =
  entireHigherDerivativeLocalSuccessorValueAtRadius
    exponentialCoefficients
    exponentialPowerSeriesEntireRepeatedFormalDerivativesUniformlyCauchy
    order (entireRadiusAt x) x (entireRadiusAt-interior x)


-- Keep the value equality separate from the derivative source equality.  This
-- avoids transporting a large proof-dependent series sum through IsDerivativeAt.
exponentialEntireHigherDerivativeLocalSuccessorValue-fixedPoint :
  ∀ order x →
  exponentialEntireHigherDerivativeLocalSuccessorValue order x
    ≡ exponentialEntireValue x
exponentialEntireHigherDerivativeLocalSuccessorValue-fixedPoint order x =
  sym
    (entireHigherDerivativeLocalSuccessorValueAtRadius-agrees
      exponentialCoefficients
      exponentialPowerSeriesEntireRepeatedFormalDerivativesUniformlyCauchy
      order (entireRadiusAt x) x (entireRadiusAt-interior x))
  ∙ exponentialEntireHigherDerivativeValue-fixedPoint (suc order) x


exponentialEntireHigherDerivativeValueHasFixedPointDerivative :
  ∀ order x →
  (exponentialEntireHigherDerivativeLocalSuccessorValue order x
      ≡ exponentialEntireValue x)
  ×
  IsDerivativeAt
    (exponentialEntireHigherDerivativeValue order)
    (exponentialEntireHigherDerivativeLocalSuccessorValue order x)
    x
exponentialEntireHigherDerivativeValueHasFixedPointDerivative order x =
  exponentialEntireHigherDerivativeLocalSuccessorValue-fixedPoint order x
  , entireHigherDerivativeValueHasSuccessorAtRadius
      exponentialCoefficients
      exponentialPowerSeriesEntireRepeatedFormalDerivativesUniformlyCauchy
      exponentialPowerSeriesEntireRepeatedDifferenceFactorsUniformlyCauchy
      order (entireRadiusAt x) x (entireRadiusAt-interior x)
