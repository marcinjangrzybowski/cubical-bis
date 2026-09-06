module Cubical.Analysis.Real.Series.PowerSeries.Exponential.Bounds.Range where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Base using (ℚ; fromNat)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.Inverse.Positive
open import Cubical.Analysis.Real.Algebra.Inverse.Order
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Real.Order.Strict.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Coefficients
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Addition
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Bounds
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Order


private
  opaque
    cancelProductMiddle : ∀ a b c → a · c ≡ 1ℝ → (a · b) · c ≡ b
    cancelProductMiddle a b c inverse =
      sym (mulAssoc a b c)
      ∙ cong (a ·_) (mulComm b c)
      ∙ mulAssoc a c b
      ∙ cong (_· b) inverse
      ∙ mulIdL b

    inverseBelowFromUpper : ∀ reciprocal target value inverse →
      reciprocal · target ≡ 1ℝ → value · inverse ≡ 1ℝ →
      0ℝ <ℝ target → 0ℝ <ℝ inverse → reciprocal <ℝ value →
      inverse <ℝ target
    inverseBelowFromUpper reciprocal target value inverse
        reciprocal-law value-law target-positive inverse-positive bound =
      subst2 _<ℝ_
        (mulIdL inverse)
        (cancelProductMiddle value target inverse value-law)
        (mulPres<PosR 1ℝ (value · target) inverse inverse-positive
          (subst (_<ℝ value · target) reciprocal-law
            (mulPres<PosR reciprocal value target target-positive bound)))


opaque
  exponentialEntireValue-upperInputBound : ∀ target → 0ℝ ≤ℝ target →
    target <ℝ exponentialEntireValue target
  exponentialEntireValue-upperInputBound target nonnegative =
    <≤ℝ-trans target (1ℝ + target) (exponentialEntireValue target)
      (subst (_<ℝ 1ℝ + target) (addIdL target)
        (<ℝ-addR 0ℝ 1ℝ target
          (<ℚ→<ℝ 0 1 (snd (exponentialPositiveNatural 0)))))
      (exponentialEntireValue-linearLowerBound target nonnegative)

  exponentialEntireValue-lowerInputBound : ∀ target (positive : 0ℝ <ℝ target) →
    exponentialEntireValue (- positiveReciprocal target positive) <ℝ target
  exponentialEntireValue-lowerInputBound target positive =
    inverseBelowFromUpper (positiveReciprocal target positive) target
      (exponentialEntireValue (positiveReciprocal target positive))
      (exponentialEntireValue (- positiveReciprocal target positive))
      (positiveReciprocalLaw' target positive)
      (exponentialEntireValue-mul-negative (positiveReciprocal target positive))
      positive (exponentialEntireValue-positive (- positiveReciprocal target positive))
      (exponentialEntireValue-upperInputBound (positiveReciprocal target positive)
        (<ℝ-weaken 0ℝ (positiveReciprocal target positive)
          (positiveReciprocalPositive target positive)))


-- An explicit finite search interval for each positive target: [-1/y,y].
-- No Archimedean bound or choice principle is needed to produce it.
exponentialPositiveTargetBracket : ∀ target → 0ℝ <ℝ target →
  Σ[ lower ∈ ℝ ] Σ[ upper ∈ ℝ ]
    (lower <ℝ upper)
    × (exponentialEntireValue lower <ℝ target)
    × (target <ℝ exponentialEntireValue upper)
exponentialPositiveTargetBracket target positive =
  (- positiveReciprocal target positive) , target
  , <ℝ-trans (- positiveReciprocal target positive) 0ℝ target
      (subst ((- positiveReciprocal target positive) <ℝ_) negZero
        (<ℝ-neg 0ℝ (positiveReciprocal target positive)
          (positiveReciprocalPositive target positive)))
      positive
  , exponentialEntireValue-lowerInputBound target positive
  , exponentialEntireValue-upperInputBound target (<ℝ-weaken 0ℝ target positive)
