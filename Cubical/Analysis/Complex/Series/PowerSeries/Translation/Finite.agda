module Cubical.Analysis.Complex.Series.PowerSeries.Translation.Finite where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat using (ℕ; suc; _∸_)
import Cubical.Data.Nat as Nat
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.Product.Finite
open import Cubical.Analysis.Complex.Series.Double.Finite
open import Cubical.Analysis.Complex.Series.PowerSeries.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Exponential.Finite using (partialSumℂ-as-finSum)
open import Cubical.Analysis.Complex.Series.PowerSeries.Translation.Coefficients
open import Cubical.Analysis.Complex.Series.PowerSeries.Translation.Base
import Cubical.Analysis.Complex.Series.PowerSeries.Translation.Algebra as Algebra

private
  module A = Algebra.TranslationAlgebra ℂCommRing

opaque
  translatedMonomialDiagonalℂ : ∀ coefficients center increment n →
    diagonalSumℂ (λ order index → translatedCoefficientTermsℂ coefficients center order index ·ℂ (increment ^ℂ order)) n
      ≡ powerSeriesTermsℂ coefficients (center +ℂ increment) n
  translatedMonomialDiagonalℂ coefficients center increment n =
    partialSumℂ-as-finSum (λ k → translatedCoefficientTermsℂ coefficients center k (n ∸ k) ·ℂ (increment ^ℂ k)) (suc n)
    ∙ A.translatedMonomialAddition coefficients binomialCoefficientℂ binomialCoefficientℂ-agreesRing center increment n

-- Truncating at original degree count gives count translated coefficients.
-- The cutoff count-order describes a triangle, not a rectangular truncation.
finiteTranslatedCoefficientsℂ : ComplexSequence → ℂ → ℕ → ComplexSequence
finiteTranslatedCoefficientsℂ coefficients center count order =
  partialSumℂ (translatedCoefficientTermsℂ coefficients center order) (count ∸ order)

opaque
  finitePowerSeriesTranslationℂ : ∀ coefficients center increment count →
    partialSumℂ (powerSeriesTermsℂ (finiteTranslatedCoefficientsℂ coefficients center count) increment) count
      ≡ partialSumℂ (powerSeriesTermsℂ coefficients (center +ℂ increment)) count
  finitePowerSeriesTranslationℂ coefficients center increment count =
    partialSumℂ-pointwise
      (powerSeriesTermsℂ (finiteTranslatedCoefficientsℂ coefficients center count) increment)
      (λ order → partialSumℂ (λ index → translatedCoefficientTermsℂ coefficients center order index ·ℂ (increment ^ℂ order)) (count ∸ order))
      (λ order → sym (partialSumℂ-right-scale (translatedCoefficientTermsℂ coefficients center order) (increment ^ℂ order) (count ∸ order))) count
    ∙ sym (partialSumℂ-diagonalSum
        (λ order index → translatedCoefficientTermsℂ coefficients center order index ·ℂ (increment ^ℂ order)) count)
    ∙ partialSumℂ-pointwise
        (diagonalSumℂ (λ order index → translatedCoefficientTermsℂ coefficients center order index ·ℂ (increment ^ℂ order)))
        (powerSeriesTermsℂ coefficients (center +ℂ increment)) (translatedMonomialDiagonalℂ coefficients center increment) count
