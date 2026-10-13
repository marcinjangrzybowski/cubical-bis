module Cubical.Analysis.Complex.Series.PowerSeries.Taylor.Elementary where

open import Cubical.Foundations.Prelude
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.Operations
open import Cubical.Analysis.Complex.Series.PowerSeries.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Elementary.Coefficients
open import Cubical.Analysis.Complex.Series.PowerSeries.Elementary.HigherDerivative
open import Cubical.Analysis.Complex.Series.PowerSeries.Exponential.HasSum
open import Cubical.Analysis.Complex.Series.PowerSeries.Trigonometric.HasSum
open import Cubical.Analysis.Complex.Series.PowerSeries.Taylor.Coefficients
open import Cubical.Analysis.Complex.Transcendental.Exponential.Base
open import Cubical.Analysis.Complex.Transcendental.Trigonometric.Base
open import Cubical.Analysis.Complex.Transcendental.HigherDerivative

-- The coefficients here explicitly use the ambient derivative towers.
exponentialTaylorAtZeroHasSum : ∀ z →
  HasComplexSum (powerSeriesTermsℂ (taylorCoefficientsℂ (λ _ → expℂ 0ℂ)) z) (expℂ z)
exponentialTaylorAtZeroHasSum z = complexPowerSeriesTaylorHasSum exponentialCoefficientsℂ
  (λ _ → expℂ 0ℂ) (λ n → exponentialRepeatedDerivativeHasSum n 0ℂ) z (expℂ z) (exponentialComplexPowerSeriesHasSum z)

sineTaylorAtZeroHasSum : ∀ z →
  HasComplexSum (powerSeriesTermsℂ (taylorCoefficientsℂ (λ n → sineDerivativeℂ n 0ℂ)) z) (sinℂ z)
sineTaylorAtZeroHasSum z = complexPowerSeriesTaylorHasSum sineCoefficientsℂ
  (λ n → sineDerivativeℂ n 0ℂ) (λ n → sineRepeatedDerivativeHasSum n 0ℂ) z (sinℂ z) (sineComplexPowerSeriesHasSum z)

cosineTaylorAtZeroHasSum : ∀ z →
  HasComplexSum (powerSeriesTermsℂ (taylorCoefficientsℂ (λ n → cosineDerivativeℂ n 0ℂ)) z) (cosℂ z)
cosineTaylorAtZeroHasSum z = complexPowerSeriesTaylorHasSum cosineCoefficientsℂ
  (λ n → cosineDerivativeℂ n 0ℂ) (λ n → cosineRepeatedDerivativeHasSum n 0ℂ) z (cosℂ z) (cosineComplexPowerSeriesHasSum z)

-- Exponential translation follows from its existing addition law. No
-- rearrangement of an infinite doubly indexed series is required.
opaque
  exponentialTaylorAtCenterHasSum : ∀ center increment →
    HasComplexSum (powerSeriesTermsℂ (taylorCoefficientsℂ (λ _ → expℂ center)) increment) (expℂ (center +ℂ increment))
  exponentialTaylorAtCenterHasSum center increment =
    subst (HasComplexSum (powerSeriesTermsℂ (taylorCoefficientsℂ (λ _ → expℂ center)) increment))
      (sym (expℂ-add center increment))
      (complexHasSumPointwise (scaleComplexSeries (expℂ center) (powerSeriesTermsℂ exponentialCoefficientsℂ increment))
        (powerSeriesTermsℂ (taylorCoefficientsℂ (λ _ → expℂ center)) increment)
        (λ n → ·ℂAssoc (expℂ center) (exponentialCoefficientsℂ n) (increment ^ℂ n)
          ∙ cong (_·ℂ (increment ^ℂ n)) (·ℂComm (expℂ center) (exponentialCoefficientsℂ n)))
        (expℂ center ·ℂ expℂ increment)
        (scaleHasComplexSum (expℂ center) (powerSeriesTermsℂ exponentialCoefficientsℂ increment) (expℂ increment)
          (exponentialComplexPowerSeriesHasSum increment)))
