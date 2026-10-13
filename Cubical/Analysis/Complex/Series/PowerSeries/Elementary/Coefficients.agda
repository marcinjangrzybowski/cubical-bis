module Cubical.Analysis.Complex.Series.PowerSeries.Elementary.Coefficients where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Algebra.CommRing
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditiveGroup using (negZero)
open import Cubical.Analysis.Real.Algebra.Natural using (realNatural)
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.CommRing
import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Coefficients as Real
import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Coefficients as Real
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Algebra.RealScalar
open import Cubical.Analysis.Complex.Conjugation
open import Cubical.Analysis.Complex.Sequence
open import Cubical.Analysis.Complex.Series.PowerSeries.RealEmbedding
open import Cubical.Analysis.Complex.Series.PowerSeries.Difference
import Cubical.Analysis.Complex.Series.PowerSeries.Elementary.Algebra as Algebra

-- Exactly the existing native real coefficients, embedded in ℂ. In
-- particular, no new factorial or even/odd indexing convention is introduced.
exponentialCoefficientsℂ sineCoefficientsℂ cosineCoefficientsℂ : ComplexSequence
exponentialCoefficientsℂ = realCoefficientsℂ Real.exponentialCoefficients
sineCoefficientsℂ = realCoefficientsℂ Real.sineCoefficients
cosineCoefficientsℂ = realCoefficientsℂ Real.cosineCoefficients

private module I = Algebra.ImaginaryPowers ℝCommRing
private module Conj = CommRingHomTheory conjugateHom

opaque
  conjugateRealCoefficient : ∀ x → conjugate (fromℝ x) ≡ fromℝ x
  conjugateRealCoefficient x = ℂ≡ refl negZero

  negativeImaginaryConjugate : -ℂ iℂ ≡ conjugate iℂ
  negativeImaginaryConjugate = ℂ≡ negZero refl

  formalDerivativeℂ-exponential : formalDerivativeℂ exponentialCoefficientsℂ ≡ exponentialCoefficientsℂ
  formalDerivativeℂ-exponential = funExt λ n →
    sym (fromℝ-pres· (realNatural (suc n)) (Real.exponentialCoefficients (suc n))) ∙ cong fromℝ (Real.exponentialCoefficients-suc n)

  formalDerivativeℂ-sine : formalDerivativeℂ sineCoefficientsℂ ≡ cosineCoefficientsℂ
  formalDerivativeℂ-sine = funExt λ n →
    sym (fromℝ-pres· (realNatural (suc n)) (Real.sineCoefficients (suc n))) ∙ cong fromℝ (Real.sineCoefficients-suc n)

  formalDerivativeℂ-cosine : formalDerivativeℂ cosineCoefficientsℂ ≡ (λ n → -ℂ sineCoefficientsℂ n)
  formalDerivativeℂ-cosine = funExt λ n →
    sym (fromℝ-pres· (realNatural (suc n)) (Real.cosineCoefficients (suc n))) ∙ cong fromℝ (Real.cosineCoefficients-suc n) ∙ ℂ≡ refl (sym negZero)

  imaginaryPower-signs : ∀ n → iℂ ^ℂ n ≡ (rat (Real.cosineRationalSign n) , rat (Real.sineRationalSign n))
  imaginaryPower-signs = I.imaginaryPower (rat ∘ Real.cosineRationalSign) (rat ∘ Real.sineRationalSign)
    refl refl (λ n → sym (neg-rat (Real.sineRationalSign n))) (λ _ → refl)

  exponentialCoefficientℂ-imaginary : ∀ n → exponentialCoefficientsℂ n ·ℂ (iℂ ^ℂ n)
    ≡ (Real.cosineCoefficients n , Real.sineCoefficients n)
  exponentialCoefficientℂ-imaginary n = cong (exponentialCoefficientsℂ n ·ℂ_) (imaginaryPower-signs n)
    ∙ ·ℂComm (exponentialCoefficientsℂ n) (rat (Real.cosineRationalSign n) , rat (Real.sineRationalSign n))
    ∙ complexMultiplyReal (rat (Real.cosineRationalSign n) , rat (Real.sineRationalSign n)) (Real.exponentialCoefficients n)
    ∙ ℂ≡ (mul-rat (Real.cosineRationalSign n) (Real.exponentialRationalCoefficient n))
          (mul-rat (Real.sineRationalSign n) (Real.exponentialRationalCoefficient n))

  exponentialCoefficientℂ-negativeImaginary : ∀ n → exponentialCoefficientsℂ n ·ℂ ((-ℂ iℂ) ^ℂ n)
    ≡ (Real.cosineCoefficients n , - Real.sineCoefficients n)
  exponentialCoefficientℂ-negativeImaginary n = cong₂ _·ℂ_
    (sym (conjugateRealCoefficient (Real.exponentialCoefficients n)))
    (cong (_^ℂ n) negativeImaginaryConjugate ∙ sym (Conj.pres^ iℂ n))
    ∙ sym (conjugate-pres· (exponentialCoefficientsℂ n) (iℂ ^ℂ n))
    ∙ cong conjugate (exponentialCoefficientℂ-imaginary n)
