module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.HigherEntire where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat as ℕ using (ℕ; zero; suc)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Majorant
open import Cubical.Analysis.Real.Series.PowerSeries.RepeatedDerivative
open import Cubical.Analysis.Real.Series.PowerSeries.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Entire.HigherDerivative
open import
  Cubical.Analysis.Real.Series.PowerSeries.Exponential.Coefficients
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Coefficients
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Convergence
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.HigherDerivative
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire


repeatedFormalDerivativePresExponentialMajorant :
  ∀ order coefficients →
  CoefficientMajorizedBy coefficients exponentialCoefficients →
  CoefficientMajorizedBy
    (repeatedFormalDerivative order coefficients)
    exponentialCoefficients
repeatedFormalDerivativePresExponentialMajorant
    zero coefficients majorized =
  majorized
repeatedFormalDerivativePresExponentialMajorant
    (suc order) coefficients majorized =
  formalDerivativePresExponentialMajorant
    (repeatedFormalDerivative order coefficients)
    (repeatedFormalDerivativePresExponentialMajorant
      order coefficients majorized)


sineRepeatedFormalDerivativeMajorizedByExponential : ∀ order →
  CoefficientMajorizedBy
    (repeatedFormalDerivative order sineCoefficients)
    exponentialCoefficients
sineRepeatedFormalDerivativeMajorizedByExponential order =
  repeatedFormalDerivativePresExponentialMajorant
    order sineCoefficients sineCoefficientsMajorizedByExponential


cosineRepeatedFormalDerivativeMajorizedByExponential : ∀ order →
  CoefficientMajorizedBy
    (repeatedFormalDerivative order cosineCoefficients)
    exponentialCoefficients
cosineRepeatedFormalDerivativeMajorizedByExponential order =
  repeatedFormalDerivativePresExponentialMajorant
    order cosineCoefficients cosineCoefficientsMajorizedByExponential


sinePowerSeriesEntireRepeatedFormalDerivativesUniformlyCauchy :
  EntireRepeatedFormalDerivativesUniformlyCauchy sineCoefficients
sinePowerSeriesEntireRepeatedFormalDerivativesUniformlyCauchy
    radius order =
  entirePowerSeriesUniformlyCauchyByExponentialMajorant
    (repeatedFormalDerivative order sineCoefficients)
    (sineRepeatedFormalDerivativeMajorizedByExponential order)
    radius


cosinePowerSeriesEntireRepeatedFormalDerivativesUniformlyCauchy :
  EntireRepeatedFormalDerivativesUniformlyCauchy cosineCoefficients
cosinePowerSeriesEntireRepeatedFormalDerivativesUniformlyCauchy
    radius order =
  entirePowerSeriesUniformlyCauchyByExponentialMajorant
    (repeatedFormalDerivative order cosineCoefficients)
    (cosineRepeatedFormalDerivativeMajorizedByExponential order)
    radius


sinePowerSeriesEntireRepeatedDifferenceFactorsUniformlyCauchy :
  EntireRepeatedFormalDerivativeDifferenceFactorsUniformlyCauchy
    sineCoefficients
sinePowerSeriesEntireRepeatedDifferenceFactorsUniformlyCauchy
    radius order =
  entireDifferenceFactorUniformlyCauchyByExponentialMajorant
    (repeatedFormalDerivative order sineCoefficients)
    (sineRepeatedFormalDerivativeMajorizedByExponential order)
    radius


cosinePowerSeriesEntireRepeatedDifferenceFactorsUniformlyCauchy :
  EntireRepeatedFormalDerivativeDifferenceFactorsUniformlyCauchy
    cosineCoefficients
cosinePowerSeriesEntireRepeatedDifferenceFactorsUniformlyCauchy
    radius order =
  entireDifferenceFactorUniformlyCauchyByExponentialMajorant
    (repeatedFormalDerivative order cosineCoefficients)
    (cosineRepeatedFormalDerivativeMajorizedByExponential order)
    radius


sineEntireHigherDerivativeValue : ℕ → ℝ → ℝ
sineEntireHigherDerivativeValue =
  entireHigherDerivativeValue
    sineCoefficients
    sinePowerSeriesEntireRepeatedFormalDerivativesUniformlyCauchy


cosineEntireHigherDerivativeValue : ℕ → ℝ → ℝ
cosineEntireHigherDerivativeValue =
  entireHigherDerivativeValue
    cosineCoefficients
    cosinePowerSeriesEntireRepeatedFormalDerivativesUniformlyCauchy


sineEntireHigherDerivativeValue-zero : ∀ x →
  sineEntireHigherDerivativeValue zero x ≡ sinℝ x
sineEntireHigherDerivativeValue-zero x =
  entirePowerSeriesValueIndependent
    sineCoefficients
    (entireRepeatedFormalDerivativeUniform
      sineCoefficients
      sinePowerSeriesEntireRepeatedFormalDerivativesUniformlyCauchy
      zero)
    sinePowerSeriesEntireUniformlyCauchy x


cosineEntireHigherDerivativeValue-zero : ∀ x →
  cosineEntireHigherDerivativeValue zero x ≡ cosℝ x
cosineEntireHigherDerivativeValue-zero x =
  entirePowerSeriesValueIndependent
    cosineCoefficients
    (entireRepeatedFormalDerivativeUniform
      cosineCoefficients
      cosinePowerSeriesEntireRepeatedFormalDerivativesUniformlyCauchy
      zero)
    cosinePowerSeriesEntireUniformlyCauchy x


sineEntireHigherDerivativeValue-addFour : ∀ order x →
  sineEntireHigherDerivativeValue (4 ℕ.+ order) x ≡
  sineEntireHigherDerivativeValue order x
sineEntireHigherDerivativeValue-addFour order x =
  entirePowerSeriesValuePresPath
    (repeatedFormalDerivative (4 ℕ.+ order) sineCoefficients)
    (repeatedFormalDerivative order sineCoefficients)
    (repeatedFormalDerivative-sine-addFour order)
    (entireRepeatedFormalDerivativeUniform
      sineCoefficients
      sinePowerSeriesEntireRepeatedFormalDerivativesUniformlyCauchy
      (4 ℕ.+ order))
    (entireRepeatedFormalDerivativeUniform
      sineCoefficients
      sinePowerSeriesEntireRepeatedFormalDerivativesUniformlyCauchy
      order) x


cosineEntireHigherDerivativeValue-addFour : ∀ order x →
  cosineEntireHigherDerivativeValue (4 ℕ.+ order) x ≡
  cosineEntireHigherDerivativeValue order x
cosineEntireHigherDerivativeValue-addFour order x =
  entirePowerSeriesValuePresPath
    (repeatedFormalDerivative (4 ℕ.+ order) cosineCoefficients)
    (repeatedFormalDerivative order cosineCoefficients)
    (repeatedFormalDerivative-cosine-addFour order)
    (entireRepeatedFormalDerivativeUniform
      cosineCoefficients
      cosinePowerSeriesEntireRepeatedFormalDerivativesUniformlyCauchy
      (4 ℕ.+ order))
    (entireRepeatedFormalDerivativeUniform
      cosineCoefficients
      cosinePowerSeriesEntireRepeatedFormalDerivativesUniformlyCauchy
      order) x
