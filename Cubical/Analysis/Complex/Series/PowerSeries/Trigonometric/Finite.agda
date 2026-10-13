module Cubical.Analysis.Complex.Series.PowerSeries.Trigonometric.Finite where

open import Cubical.Foundations.Prelude
open import Cubical.Analysis.Real.Algebra.CommRing
import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Coefficients as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Transcendental.Trigonometric.Constants
open import Cubical.Analysis.Complex.Transcendental.Trigonometric.Base
import Cubical.Analysis.Complex.Transcendental.Trigonometric.Algebra as Trig
open import Cubical.Analysis.Complex.Series.PowerSeries.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Rescaling
open import Cubical.Analysis.Complex.Series.PowerSeries.Elementary.Coefficients
import Cubical.Analysis.Complex.Series.PowerSeries.Elementary.Algebra as Algebra

private
  module A = Algebra.FiniteAlgebra ℂCommRing
  module T = Trig.RealRestriction ℝCommRing

-- Apply the existing Euler coefficient algebra before taking limits. The
-- masks are the native real coefficients, with their original indexing.
opaque
  cosineExponentialTermsℂ : ∀ z n →
    cosFromExp (powerSeriesTermsℂ exponentialCoefficientsℂ (iℂ ·ℂ z) n)
      (powerSeriesTermsℂ exponentialCoefficientsℂ ((-ℂ iℂ) ·ℂ z) n)
      ≡ powerSeriesTermsℂ cosineCoefficientsℂ z n
  cosineExponentialTermsℂ z n = cong₂ cosFromExp
    (powerSeriesTermsℂ-rescale iℂ exponentialCoefficientsℂ z n)
    (powerSeriesTermsℂ-rescale (-ℂ iℂ) exponentialCoefficientsℂ z n)
    ∙ A.cosPairRightScale halfℂ (exponentialCoefficientsℂ n ·ℂ (iℂ ^ℂ n))
        (exponentialCoefficientsℂ n ·ℂ ((-ℂ iℂ) ^ℂ n)) (z ^ℂ n)
    ∙ cong (_·ℂ (z ^ℂ n))
        (cong₂ cosFromExp (exponentialCoefficientℂ-imaginary n) (exponentialCoefficientℂ-negativeImaginary n)
        ∙ T.cosPair-real halfℝ halfℝ-double (Real.cosineCoefficients n) (Real.sineCoefficients n))

  sineExponentialTermsℂ : ∀ z n →
    sinFromExp (powerSeriesTermsℂ exponentialCoefficientsℂ (iℂ ·ℂ z) n)
      (powerSeriesTermsℂ exponentialCoefficientsℂ ((-ℂ iℂ) ·ℂ z) n)
      ≡ powerSeriesTermsℂ sineCoefficientsℂ z n
  sineExponentialTermsℂ z n = cong₂ sinFromExp
    (powerSeriesTermsℂ-rescale iℂ exponentialCoefficientsℂ z n)
    (powerSeriesTermsℂ-rescale (-ℂ iℂ) exponentialCoefficientsℂ z n)
    ∙ A.sinPairRightScale halfℂ iℂ (exponentialCoefficientsℂ n ·ℂ (iℂ ^ℂ n))
        (exponentialCoefficientsℂ n ·ℂ ((-ℂ iℂ) ^ℂ n)) (z ^ℂ n)
    ∙ cong (_·ℂ (z ^ℂ n))
        (cong₂ sinFromExp (exponentialCoefficientℂ-imaginary n) (exponentialCoefficientℂ-negativeImaginary n)
        ∙ T.sinPair-real halfℝ halfℝ-double (Real.cosineCoefficients n) (Real.sineCoefficients n))
