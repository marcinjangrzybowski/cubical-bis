module Cubical.Analysis.Complex.Series.PowerSeries.RealEmbedding where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Algebra.CommRing
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Functions.Powers
import Cubical.Analysis.Real.Series.Base as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Polar.Cis using (fromℝ-naturalPower)
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Base
import Cubical.Analysis.Real.Series.PowerSeries.Base as Real

-- Embed the existing real coefficient sequence and its sum, rather than
-- rebuilding either completion or a separate real-axis power series.
realCoefficientsℂ : Real.RealSequence → ℕ → ℂ
realCoefficientsℂ coefficients = fromℝ ∘ coefficients

opaque
  realPowerSeriesTermℂ : ∀ coefficients x n →
    powerSeriesTermsℂ (realCoefficientsℂ coefficients) (fromℝ x) n
      ≡ fromℝ (Real.powerSeriesTerms coefficients x n)
  realPowerSeriesTermℂ coefficients x n =
    cong (fromℝ (coefficients n) ·ℂ_) (fromℝ-naturalPower x n)
    ∙ sym (fromℝ-pres· (coefficients n) (powℝ x n))

fromℝHasComplexSum : ∀ terms value → Real.HasSum terms value →
  HasComplexSum (fromℝ ∘ terms) (fromℝ value)
fromℝHasComplexSum terms value summed = summed , snd Real.zeroSeriesSummable

realPowerSeriesHasComplexSum : ∀ coefficients x value →
  Real.HasSum (Real.powerSeriesTerms coefficients x) value →
  HasComplexSum (powerSeriesTermsℂ (realCoefficientsℂ coefficients) (fromℝ x)) (fromℝ value)
realPowerSeriesHasComplexSum coefficients x value summed =
  complexHasSumPointwise (fromℝ ∘ Real.powerSeriesTerms coefficients x)
    (powerSeriesTermsℂ (realCoefficientsℂ coefficients) (fromℝ x))
    (λ n → sym (realPowerSeriesTermℂ coefficients x n)) (fromℝ value)
    (fromℝHasComplexSum (Real.powerSeriesTerms coefficients x) value summed)
