module Cubical.Analysis.Complex.Series.PowerSeries.Elementary.HigherDerivative where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (zero; suc)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.Operations
open import Cubical.Analysis.Complex.Series.PowerSeries.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Difference
open import Cubical.Analysis.Complex.Series.PowerSeries.RepeatedDerivative
open import Cubical.Analysis.Complex.Series.PowerSeries.Elementary.Coefficients
open import Cubical.Analysis.Complex.Series.PowerSeries.Exponential.HasSum
open import Cubical.Analysis.Complex.Series.PowerSeries.Trigonometric.HasSum
open import Cubical.Analysis.Complex.Transcendental.Exponential.Base
open import Cubical.Analysis.Complex.Transcendental.Trigonometric.Base
open import Cubical.Analysis.Complex.Transcendental.HigherDerivative

opaque
  repeatedFormalDerivativeℂ-exponential : ∀ n →
    repeatedFormalDerivativeℂ n exponentialCoefficientsℂ ≡ exponentialCoefficientsℂ
  repeatedFormalDerivativeℂ-exponential zero = refl
  repeatedFormalDerivativeℂ-exponential (suc n) = repeatedFormalDerivativeℂ-successor n exponentialCoefficientsℂ
    ∙ cong formalDerivativeℂ (repeatedFormalDerivativeℂ-exponential n) ∙ formalDerivativeℂ-exponential

exponentialRepeatedDerivativeHasSum : ∀ n z →
  HasComplexSum (powerSeriesTermsℂ (repeatedFormalDerivativeℂ n exponentialCoefficientsℂ) z) (expℂ z)
exponentialRepeatedDerivativeHasSum n z = subst (λ c → HasComplexSum (powerSeriesTermsℂ c z) (expℂ z))
  (sym (repeatedFormalDerivativeℂ-exponential n)) (exponentialComplexPowerSeriesHasSum z)

private
  negatedCoefficientsHaveSum : ∀ coefficients z value → HasComplexSum (powerSeriesTermsℂ coefficients z) value →
    HasComplexSum (powerSeriesTermsℂ (λ n → -ℂ coefficients n) z) (-ℂ value)
  negatedCoefficientsHaveSum coefficients z value summed = complexHasSumPointwise
    (λ n → -ℂ powerSeriesTermsℂ coefficients z n) (powerSeriesTermsℂ (λ n → -ℂ coefficients n) z)
    (λ n → sym (ℂRing.-DistL· (coefficients n) (z ^ℂ n))) (-ℂ value)
    (negHasComplexSum (powerSeriesTermsℂ coefficients z) value summed)

-- The recurrences identify every formal-derivative sum with the explicit
-- ambient derivative towers. Thus the higher-series values describe the
-- existing elementary functions and their actual complex derivatives.
mutual
  sineRepeatedDerivativeHasSum : ∀ n z →
    HasComplexSum (powerSeriesTermsℂ (repeatedFormalDerivativeℂ n sineCoefficientsℂ) z) (sineDerivativeℂ n z)
  sineRepeatedDerivativeHasSum zero = sineComplexPowerSeriesHasSum
  sineRepeatedDerivativeHasSum (suc n) z =
    subst (λ c → HasComplexSum (powerSeriesTermsℂ c z) (sineDerivativeℂ (suc n) z))
      (sym (repeatedFormalDerivativeℂ-commute n sineCoefficientsℂ
        ∙ cong (repeatedFormalDerivativeℂ n) formalDerivativeℂ-sine)) (cosineRepeatedDerivativeHasSum n z)

  cosineRepeatedDerivativeHasSum : ∀ n z →
    HasComplexSum (powerSeriesTermsℂ (repeatedFormalDerivativeℂ n cosineCoefficientsℂ) z) (cosineDerivativeℂ n z)
  cosineRepeatedDerivativeHasSum zero = cosineComplexPowerSeriesHasSum
  cosineRepeatedDerivativeHasSum (suc n) z =
    subst (λ c → HasComplexSum (powerSeriesTermsℂ c z) (cosineDerivativeℂ (suc n) z))
      (sym (repeatedFormalDerivativeℂ-commute n cosineCoefficientsℂ
        ∙ cong (repeatedFormalDerivativeℂ n) formalDerivativeℂ-cosine
        ∙ repeatedFormalDerivativeℂ-neg n sineCoefficientsℂ))
      (negatedCoefficientsHaveSum (repeatedFormalDerivativeℂ n sineCoefficientsℂ) z (sineDerivativeℂ n z)
        (sineRepeatedDerivativeHasSum n z))
