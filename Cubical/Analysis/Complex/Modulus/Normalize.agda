module Cubical.Analysis.Complex.Modulus.Normalize where

open import Cubical.Foundations.Prelude
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Inverse.Positive
open import Cubical.Analysis.Real.Algebra.Inverse.Order
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Modulus.Base

private
  inverseModulus : (z : ℂ) → 0ℝ <ℝ modulusℂ z → ℝ
  inverseModulus z positive = positiveReciprocal (modulusℂ z) positive

opaque
  normalizeℂ : (z : ℂ) → 0ℝ <ℝ modulusℂ z → ℂ
  normalizeℂ z positive = fromℝ (inverseModulus z positive) ·ℂ z

  modulusℂ-normalize : ∀ z positive → modulusℂ (normalizeℂ z positive) ≡ 1ℝ
  modulusℂ-normalize z positive = modulusℂ-mul (fromℝ reciprocal) z
    ∙ cong (_· modulusℂ z)
      (modulusℂ-fromℝ reciprocal ∙ absOfNonnegative reciprocal
        (<ℝ-weaken 0ℝ reciprocal (positiveReciprocalPositive (modulusℂ z) positive)))
    ∙ mulComm reciprocal (modulusℂ z) ∙ positiveReciprocalLaw (modulusℂ z) positive
    where
    reciprocal : ℝ
    reciprocal = inverseModulus z positive

  normalizeℂ-reconstruct : ∀ z positive →
    fromℝ (modulusℂ z) ·ℂ normalizeℂ z positive ≡ z
  normalizeℂ-reconstruct z positive =
    ·ℂAssoc (fromℝ (modulusℂ z)) (fromℝ (inverseModulus z positive)) z
      ∙ cong (_·ℂ z)
        (sym (fromℝ-pres· (modulusℂ z) (inverseModulus z positive))
          ∙ cong fromℝ (positiveReciprocalLaw (modulusℂ z) positive))
      ∙ ·ℂComm 1ℂ z ∙ ·ℂIdR z
