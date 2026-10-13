module Cubical.Analysis.Complex.Series.PowerSeries.Rescaling where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Base

rescaleComplexCoefficients : ℂ → ComplexSequence → ComplexSequence
rescaleComplexCoefficients c coefficients n = coefficients n ·ℂ (c ^ℂ n)

private module P = Exponentiation ℂCommRing

opaque
  powerSeriesTermsℂ-rescale : ∀ c coefficients z n →
    powerSeriesTermsℂ coefficients (c ·ℂ z) n
      ≡ powerSeriesTermsℂ (rescaleComplexCoefficients c coefficients) z n
  powerSeriesTermsℂ-rescale c coefficients z n =
    cong (coefficients n ·ℂ_) (P.^-ldist-· c z n)
    ∙ ·ℂAssoc (coefficients n) (c ^ℂ n) (z ^ℂ n)

rescaleComplexPowerSeriesHasSum : ∀ c coefficients z value →
  HasComplexSum (powerSeriesTermsℂ coefficients (c ·ℂ z)) value →
  HasComplexSum (powerSeriesTermsℂ (rescaleComplexCoefficients c coefficients) z) value
rescaleComplexPowerSeriesHasSum c coefficients z value = complexHasSumPointwise
  (powerSeriesTermsℂ coefficients (c ·ℂ z)) (powerSeriesTermsℂ (rescaleComplexCoefficients c coefficients) z)
  (powerSeriesTermsℂ-rescale c coefficients z) value
