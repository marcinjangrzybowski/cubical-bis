module Cubical.Analysis.Complex.Series.PowerSeries.Taylor.Coefficients where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Analysis.Real.Algebra.Multiplication using (_·_)
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ; mulComm)
open import Cubical.Analysis.Real.Algebra.Natural
import Cubical.Analysis.Real.Series.PowerSeries.RepeatedDerivative as Real
import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Coefficients as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Series.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.Base
open import Cubical.Analysis.Complex.Series.PowerSeries.AtZero
open import Cubical.Analysis.Complex.Series.PowerSeries.Elementary.Coefficients
open import Cubical.Analysis.Complex.Series.PowerSeries.RepeatedDerivative
open import Cubical.Analysis.Complex.Series.PowerSeries.Difference using (formalDerivativeℂ)

-- Multiplication by the existing embedded 1/n! avoids division by an
-- arbitrary complex value and retains the native factorial convention.
taylorCoefficientsℂ : (ℕ → ℂ) → ComplexSequence
taylorCoefficientsℂ derivativesAtCenter n = exponentialCoefficientsℂ n ·ℂ derivativesAtCenter n

private
  opaque
    inverseDerivativeMultiplier : ∀ n →
      Real.exponentialCoefficients n · realNatural (Real.derivativeNaturalProduct zero n) ≡ 1ℝ
    inverseDerivativeMultiplier n = mulComm (Real.exponentialCoefficients n) (realNatural (Real.derivativeNaturalProduct zero n))
      ∙ sym (Real.repeatedFormalDerivative-coefficient n Real.exponentialCoefficients zero)
      ∙ funExt⁻ (Real.repeatedFormalDerivative-exponentialCoefficients n) zero ∙ Real.exponentialCoefficients-zero

opaque
  normalizedRepeatedCoefficientAtZero : ∀ coefficients n →
    exponentialCoefficientsℂ n ·ℂ repeatedFormalDerivativeℂ n coefficients zero ≡ coefficients n
  normalizedRepeatedCoefficientAtZero coefficients n =
    cong (exponentialCoefficientsℂ n ·ℂ_) (repeatedFormalDerivativeℂ-coefficient n coefficients zero)
    ∙ ·ℂAssoc (exponentialCoefficientsℂ n) (fromℝ (realNatural (Real.derivativeNaturalProduct zero n))) (coefficients n)
    ∙ cong (_·ℂ coefficients n)
        (sym (fromℝ-pres· (Real.exponentialCoefficients n) (realNatural (Real.derivativeNaturalProduct zero n)))
        ∙ cong fromℝ (inverseDerivativeMultiplier n))
    ∙ ·ℂComm 1ℂ (coefficients n) ∙ ·ℂIdR (coefficients n)

  complexPowerSeriesTaylorCoefficients : ∀ coefficients derivativesAtZero →
    (∀ n → HasComplexSum (powerSeriesTermsℂ (repeatedFormalDerivativeℂ n coefficients) 0ℂ) (derivativesAtZero n)) →
    taylorCoefficientsℂ derivativesAtZero ≡ coefficients
  complexPowerSeriesTaylorCoefficients coefficients derivativesAtZero sums = funExt λ n →
    cong (exponentialCoefficientsℂ n ·ℂ_)
      (complexPowerSeriesValueAtZero (repeatedFormalDerivativeℂ n coefficients) (derivativesAtZero n) (sums n))
    ∙ normalizedRepeatedCoefficientAtZero coefficients n

complexPowerSeriesTaylorHasSum : ∀ coefficients derivativesAtZero →
  (∀ n → HasComplexSum (powerSeriesTermsℂ (repeatedFormalDerivativeℂ n coefficients) 0ℂ) (derivativesAtZero n)) →
  ∀ z value → HasComplexSum (powerSeriesTermsℂ coefficients z) value →
  HasComplexSum (powerSeriesTermsℂ (taylorCoefficientsℂ derivativesAtZero) z) value
complexPowerSeriesTaylorHasSum coefficients derivativesAtZero sums z value =
  subst (λ c → HasComplexSum (powerSeriesTermsℂ c z) value)
    (sym (complexPowerSeriesTaylorCoefficients coefficients derivativesAtZero sums))

-- Normalizing a derivative tower commutes with shifting that tower. This
-- is the existing factorial recurrence, valid for any sequence of values.
opaque
  taylorCoefficientsℂ-zero : ∀ derivatives → taylorCoefficientsℂ derivatives zero ≡ derivatives zero
  taylorCoefficientsℂ-zero derivatives =
    cong (λ scalar → fromℝ scalar ·ℂ derivatives zero) Real.exponentialCoefficients-zero
    ∙ ·ℂComm 1ℂ (derivatives zero) ∙ ·ℂIdR (derivatives zero)

  formalDerivativeℂ-taylorCoefficients : ∀ derivatives →
    formalDerivativeℂ (taylorCoefficientsℂ derivatives) ≡ taylorCoefficientsℂ (derivatives ∘ suc)
  formalDerivativeℂ-taylorCoefficients derivatives = funExt λ n →
    ·ℂAssoc (fromℝ (realNatural (suc n))) (exponentialCoefficientsℂ (suc n)) (derivatives (suc n))
    ∙ cong (_·ℂ derivatives (suc n)) (funExt⁻ formalDerivativeℂ-exponential n)
