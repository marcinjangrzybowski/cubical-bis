module Cubical.Analysis.Complex.Series.PowerSeries.Exponential.Imaginary where

open import Cubical.Foundations.Prelude
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Functions.Powers using (powℝ)
open import Cubical.Analysis.Real.Functions.Exponential using (expℝ)
import Cubical.Analysis.Real.Series.PowerSeries.Base as Real
import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Coefficients as Real
import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Addition as Real
import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Coefficients as Real
import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Algebra.RealScalar
open import Cubical.Analysis.Complex.Polar.Cis
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.RealEmbedding
open import Cubical.Analysis.Complex.Series.PowerSeries.Rescaling
open import Cubical.Analysis.Complex.Series.PowerSeries.Elementary.Coefficients

-- The full coefficient masks (including their zero entries) identify each
-- coordinate directly. No infinite even/odd reindexing is needed.
opaque
  exponentialImaginaryTermℂ : ∀ y n →
    powerSeriesTermsℂ exponentialCoefficientsℂ (iℂ ·ℂ fromℝ y) n ≡
      (Real.powerSeriesTerms Real.cosineCoefficients y n ,
       Real.powerSeriesTerms Real.sineCoefficients y n)
  exponentialImaginaryTermℂ y n =
    powerSeriesTermsℂ-rescale iℂ exponentialCoefficientsℂ (fromℝ y) n
    ∙ cong₂ _·ℂ_ (exponentialCoefficientℂ-imaginary n) (fromℝ-naturalPower y n)
    ∙ complexMultiplyReal (Real.cosineCoefficients n , Real.sineCoefficients n) (powℝ y n)

  exponentialComplexSeriesHasSumReal : ∀ x →
    HasComplexSum (powerSeriesTermsℂ exponentialCoefficientsℂ (fromℝ x)) (fromℝ (expℝ x))
  exponentialComplexSeriesHasSumReal x = realPowerSeriesHasComplexSum
    Real.exponentialCoefficients x (expℝ x) (Real.exponentialEntirePowerSeriesHasSum x)

  exponentialComplexSeriesHasSumImaginary : ∀ y →
    HasComplexSum (powerSeriesTermsℂ exponentialCoefficientsℂ (iℂ ·ℂ fromℝ y)) (cisℝ y)
  exponentialComplexSeriesHasSumImaginary y =
    subst (HasComplexSum (powerSeriesTermsℂ exponentialCoefficientsℂ (iℂ ·ℂ fromℝ y)))
      (sym (cisℝ-value y))
      (complexHasSumPointwise
        (λ n → Real.powerSeriesTerms Real.cosineCoefficients y n , Real.powerSeriesTerms Real.sineCoefficients y n)
        (powerSeriesTermsℂ exponentialCoefficientsℂ (iℂ ·ℂ fromℝ y))
        (λ n → sym (exponentialImaginaryTermℂ y n)) (Real.cosℝ y , Real.sinℝ y)
        (Real.cosinePowerSeriesHasSum y , Real.sinePowerSeriesHasSum y))
