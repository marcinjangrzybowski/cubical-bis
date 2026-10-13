module Cubical.Analysis.Complex.Series.PowerSeries.Taylor.Elementary.Translation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.Operations
open import Cubical.Analysis.Complex.Series.PowerSeries.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Operations
open import Cubical.Analysis.Complex.Series.PowerSeries.Elementary.Coefficients
open import Cubical.Analysis.Complex.Series.PowerSeries.Elementary.HigherDerivative
open import Cubical.Analysis.Complex.Series.PowerSeries.Trigonometric.HasSum
open import Cubical.Analysis.Complex.Series.PowerSeries.Taylor.Coefficients
open import Cubical.Analysis.Complex.Transcendental.Trigonometric.Base
open import Cubical.Analysis.Complex.Transcendental.Trigonometric.Identities
open import Cubical.Analysis.Complex.Transcendental.HigherDerivative
open import Cubical.Analysis.Complex.Transcendental.HigherDerivative.Addition

private
  sineNormalized : ∀ n → exponentialCoefficientsℂ n ·ℂ sineDerivativeℂ n 0ℂ ≡ sineCoefficientsℂ n
  sineNormalized n = funExt⁻ (complexPowerSeriesTaylorCoefficients sineCoefficientsℂ
    (λ k → sineDerivativeℂ k 0ℂ) (λ k → sineRepeatedDerivativeHasSum k 0ℂ)) n

  cosineNormalized : ∀ n → exponentialCoefficientsℂ n ·ℂ cosineDerivativeℂ n 0ℂ ≡ cosineCoefficientsℂ n
  cosineNormalized n = funExt⁻ (complexPowerSeriesTaylorCoefficients cosineCoefficientsℂ
    (λ k → cosineDerivativeℂ k 0ℂ) (λ k → cosineRepeatedDerivativeHasSum k 0ℂ)) n

-- Finite addition laws identify the translated coefficients. The factorial
-- normalization is the same one used by the general Taylor API.
opaque
  sineTaylorCoefficientsAtCenter : ∀ center →
    taylorCoefficientsℂ (λ n → sineDerivativeℂ n center) ≡
      (λ n → cosℂ center ·ℂ sineCoefficientsℂ n +ℂ sinℂ center ·ℂ cosineCoefficientsℂ n)
  sineTaylorCoefficientsAtCenter center = funExt λ n →
    cong (exponentialCoefficientsℂ n ·ℂ_)
      (cong (sineDerivativeℂ n) (sym (+ℂComm 0ℂ center ∙ +ℂIdR center)) ∙ sineDerivativeℂ-add n 0ℂ center)
    ∙ ·ℂDistR+ (exponentialCoefficientsℂ n)
        (sineDerivativeℂ n 0ℂ ·ℂ cosℂ center) (cosineDerivativeℂ n 0ℂ ·ℂ sinℂ center)
    ∙ cong₂ _+ℂ_
        (·ℂAssoc (exponentialCoefficientsℂ n) (sineDerivativeℂ n 0ℂ) (cosℂ center)
          ∙ cong (_·ℂ cosℂ center) (sineNormalized n) ∙ ·ℂComm (sineCoefficientsℂ n) (cosℂ center))
        (·ℂAssoc (exponentialCoefficientsℂ n) (cosineDerivativeℂ n 0ℂ) (sinℂ center)
          ∙ cong (_·ℂ sinℂ center) (cosineNormalized n) ∙ ·ℂComm (cosineCoefficientsℂ n) (sinℂ center))

  cosineTaylorCoefficientsAtCenter : ∀ center →
    taylorCoefficientsℂ (λ n → cosineDerivativeℂ n center) ≡
      (λ n → cosℂ center ·ℂ cosineCoefficientsℂ n -ℂ sinℂ center ·ℂ sineCoefficientsℂ n)
  cosineTaylorCoefficientsAtCenter center = funExt λ n →
    cong (exponentialCoefficientsℂ n ·ℂ_)
      (cong (cosineDerivativeℂ n) (sym (+ℂComm 0ℂ center ∙ +ℂIdR center)) ∙ cosineDerivativeℂ-add n 0ℂ center)
    ∙ ℂRing.·DistR- (exponentialCoefficientsℂ n)
        (cosineDerivativeℂ n 0ℂ ·ℂ cosℂ center) (sineDerivativeℂ n 0ℂ ·ℂ sinℂ center)
    ∙ cong₂ _-ℂ_
        (·ℂAssoc (exponentialCoefficientsℂ n) (cosineDerivativeℂ n 0ℂ) (cosℂ center)
          ∙ cong (_·ℂ cosℂ center) (cosineNormalized n) ∙ ·ℂComm (cosineCoefficientsℂ n) (cosℂ center))
        (·ℂAssoc (exponentialCoefficientsℂ n) (sineDerivativeℂ n 0ℂ) (sinℂ center)
          ∙ cong (_·ℂ sinℂ center) (sineNormalized n) ∙ ·ℂComm (sineCoefficientsℂ n) (sinℂ center))

-- These are Taylor representations at every complex center, for arbitrary
-- complex increments. Only the established native sine/cosine series and
-- their linear operations are used; no infinite reindexing is assumed.
sineTaylorAtCenterHasSum : ∀ center increment →
  HasComplexSum (powerSeriesTermsℂ (taylorCoefficientsℂ (λ n → sineDerivativeℂ n center)) increment)
    (sinℂ (center +ℂ increment))
sineTaylorAtCenterHasSum center increment = subst2
  (λ coefficients value → HasComplexSum (powerSeriesTermsℂ coefficients increment) value)
  (sym (sineTaylorCoefficientsAtCenter center))
  (+ℂComm (cosℂ center ·ℂ sinℂ increment) (sinℂ center ·ℂ cosℂ increment) ∙ sym (sinℂ-add center increment))
  (addComplexPowerSeriesHasSum (scaleComplexSeries (cosℂ center) sineCoefficientsℂ)
    (scaleComplexSeries (sinℂ center) cosineCoefficientsℂ) increment
    (cosℂ center ·ℂ sinℂ increment) (sinℂ center ·ℂ cosℂ increment)
    (scaleComplexPowerSeriesHasSum (cosℂ center) sineCoefficientsℂ increment (sinℂ increment)
      (sineComplexPowerSeriesHasSum increment))
    (scaleComplexPowerSeriesHasSum (sinℂ center) cosineCoefficientsℂ increment (cosℂ increment)
      (cosineComplexPowerSeriesHasSum increment)))

cosineTaylorAtCenterHasSum : ∀ center increment →
  HasComplexSum (powerSeriesTermsℂ (taylorCoefficientsℂ (λ n → cosineDerivativeℂ n center)) increment)
    (cosℂ (center +ℂ increment))
cosineTaylorAtCenterHasSum center increment = subst2
  (λ coefficients value → HasComplexSum (powerSeriesTermsℂ coefficients increment) value)
  (sym (cosineTaylorCoefficientsAtCenter center)) (sym (cosℂ-add center increment))
  (subComplexPowerSeriesHasSum (scaleComplexSeries (cosℂ center) cosineCoefficientsℂ)
    (scaleComplexSeries (sinℂ center) sineCoefficientsℂ) increment
    (cosℂ center ·ℂ cosℂ increment) (sinℂ center ·ℂ sinℂ increment)
    (scaleComplexPowerSeriesHasSum (cosℂ center) cosineCoefficientsℂ increment (cosℂ increment)
      (cosineComplexPowerSeriesHasSum increment))
    (scaleComplexPowerSeriesHasSum (sinℂ center) sineCoefficientsℂ increment (sinℂ increment)
      (sineComplexPowerSeriesHasSum increment)))
