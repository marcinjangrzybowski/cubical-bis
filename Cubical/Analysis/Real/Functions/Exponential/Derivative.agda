module Cubical.Analysis.Real.Functions.Exponential.Derivative where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (zero; suc)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Calculus.Derivative.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Derivative
open import Cubical.Analysis.Real.Series.PowerSeries.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Coefficients
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Archimedean
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Entire
open import Cubical.Analysis.Real.Functions.Exponential


private
  derivativeUniform :
    EntireFormalDerivativePowerSeriesUniformlyCauchy exponentialCoefficients
  derivativeUniform radius =
    exponentialPowerSeriesEntireRepeatedFormalDerivativesUniformlyCauchy
      radius (suc zero)

  localDerivative : ℝ → ℝ
  localDerivative x =
    entireFormalDerivativeValueAtRadius exponentialCoefficients derivativeUniform
      (entireRadiusAt x) x (entireRadiusAt-interior x)

  -- Seal the equality separately from its transport through the remainder
  -- predicate; otherwise completed-series uniqueness is repeatedly unfolded.
  opaque
    localDerivative-value : ∀ x → localDerivative x ≡ expℝ x
    localDerivative-value x =
      sym (entireFormalDerivativeValueAtRadius-agrees
        exponentialCoefficients derivativeUniform
        (entireRadiusAt x) x (entireRadiusAt-interior x))
      ∙ entirePowerSeriesValuePresPath
          (formalDerivative exponentialCoefficients) exponentialCoefficients
          formalDerivative-exponentialCoefficients
          derivativeUniform exponentialPowerSeriesEntireUniformlyCauchy x

    localDerivative-correct : ∀ x → IsDerivativeAt expℝ (localDerivative x) x
    localDerivative-correct x =
      entirePowerSeriesValueHasFormalDerivativeAtRadius
        exponentialCoefficients exponentialPowerSeriesEntireUniformlyCauchy
        derivativeUniform exponentialPowerSeriesDifferenceFactorEntireUniformlyCauchy
        (entireRadiusAt x) x (entireRadiusAt-interior x)


opaque
  exponentialHasSelfDerivative : IsDerivative expℝ expℝ
  exponentialHasSelfDerivative x =
    subst (λ derivative-value → IsDerivativeAt expℝ derivative-value x)
      (localDerivative-value x) (localDerivative-correct x)
