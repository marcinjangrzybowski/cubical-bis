module Cubical.Analysis.Complex.Series.PowerSeries.AtZero where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat using (zero)
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Functions.Powers using (powℝ)
import Cubical.Analysis.Real.Series.PowerSeries.Base as Real
import Cubical.Analysis.Real.Series.PowerSeries.AtZero as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Algebra.RealScalar
open import Cubical.Analysis.Complex.Polar.Cis using (fromℝ-naturalPower)
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Base

-- Transfer the real zero-argument theorem coordinatewise; no new finite
-- support convergence argument is needed.
opaque
  complexPowerSeriesAtZeroHasSum : ∀ coefficients →
    HasComplexSum (powerSeriesTermsℂ coefficients 0ℂ) (coefficients zero)
  complexPowerSeriesAtZeroHasSum coefficients = complexHasSumPointwise
    (λ n → Real.powerSeriesTerms (re ∘ coefficients) 0ℝ n , Real.powerSeriesTerms (im ∘ coefficients) 0ℝ n)
    (powerSeriesTermsℂ coefficients 0ℂ)
    (λ n → sym (cong (coefficients n ·ℂ_) (fromℝ-naturalPower 0ℝ n)
      ∙ complexMultiplyReal (coefficients n) (powℝ 0ℝ n))) (coefficients zero)
    (Real.powerSeriesAtZeroHasSum (re ∘ coefficients) , Real.powerSeriesAtZeroHasSum (im ∘ coefficients))

complexPowerSeriesValueAtZero : ∀ coefficients value →
  HasComplexSum (powerSeriesTermsℂ coefficients 0ℂ) value → value ≡ coefficients zero
complexPowerSeriesValueAtZero coefficients value summed = complexSumUnique
  (powerSeriesTermsℂ coefficients 0ℂ) value (coefficients zero) summed (complexPowerSeriesAtZeroHasSum coefficients)
