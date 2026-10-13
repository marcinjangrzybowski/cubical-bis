module Cubical.Analysis.Complex.Inverse where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing using (module Units)
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Inverse.Positive
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Conjugation
open import Cubical.Analysis.Complex.NormSquared

-- Positivity of the squared norm is an apartness witness. Mere inequality
-- z ≢ 0ℂ is not enough to construct a reciprocal.
ComplexNonzero : ℂ → Type₀
ComplexNonzero z = 0ℝ <ℝ normSq z

isPropComplexNonzero : ∀ z → isProp (ComplexNonzero z)
isPropComplexNonzero z = isProp<ℝ 0ℝ (normSq z)

inverseℂ : (z : ℂ) → ComplexNonzero z → ℂ
inverseℂ z nonzero = fromℝ (positiveReciprocal (normSq z) nonzero) ·ℂ conjugate z

opaque
  inverseℂ-law : (z : ℂ) (nonzero : ComplexNonzero z) → z ·ℂ inverseℂ z nonzero ≡ 1ℂ
  inverseℂ-law z nonzero =
    ·ℂAssoc z (fromℝ reciprocal) (conjugate z)
    ∙ cong (_·ℂ conjugate z) (·ℂComm z (fromℝ reciprocal))
    ∙ sym (·ℂAssoc (fromℝ reciprocal) z (conjugate z))
    ∙ cong (fromℝ reciprocal ·ℂ_) (mul-conjugate z)
    ∙ sym (fromℝ-pres· reciprocal (normSq z))
    ∙ cong fromℝ (positiveReciprocalLaw' (normSq z) nonzero)
    where
    reciprocal : ℝ
    reciprocal = positiveReciprocal (normSq z) nonzero

  inverseℂ-law' : (z : ℂ) (nonzero : ComplexNonzero z) → inverseℂ z nonzero ·ℂ z ≡ 1ℂ
  inverseℂ-law' z nonzero = ·ℂComm (inverseℂ z nonzero) z ∙ inverseℂ-law z nonzero

  inverseℂ-unique : (z : ℂ) (nonzero : ComplexNonzero z) (w : ℂ) →
    z ·ℂ w ≡ 1ℂ → w ≡ inverseℂ z nonzero
  inverseℂ-unique z nonzero w zw = cong fst
    (Units.inverseUniqueness ℂCommRing z
      (w , zw) (inverseℂ z nonzero , inverseℂ-law z nonzero))

  inverseℂ-independent : (z : ℂ) (p q : ComplexNonzero z) → inverseℂ z p ≡ inverseℂ z q
  inverseℂ-independent z p q = cong (inverseℂ z) (isPropComplexNonzero z p q)
