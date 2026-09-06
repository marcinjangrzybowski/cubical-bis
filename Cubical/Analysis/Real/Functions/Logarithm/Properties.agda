module Cubical.Analysis.Real.Functions.Logarithm.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (1₊)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.Positive
open import Cubical.Analysis.Real.Algebra.Inverse.Positive
open import Cubical.Analysis.Real.Algebra.Inverse.Order
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Continuity
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Addition
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Order
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Continuity
open import Cubical.Analysis.Real.Functions.Exponential
open import Cubical.Analysis.Real.Functions.Logarithm.Base


private
  opaque
    positiveRatOneValue : fst (positiveRat 1₊) ≡ 1ℝ
    positiveRatOneValue = refl

    additiveInverseFromSumZero : ∀ a b → a + b ≡ 0ℝ → b ≡ - a
    additiveInverseFromSumZero a b sum-zero =
      sym (addIdL b)
      ∙ cong (_+ b) (sym (addInvL a))
      ∙ sym (addAssoc (- a) a b)
      ∙ cong ((- a) +_) sum-zero
      ∙ addIdR (- a)


opaque
  logarithm-unique : ∀ equivalent value x → expℝ x ≡ fst value →
    logarithmFromEquivalence equivalent value ≡ x
  logarithm-unique equivalent value x exponential-value =
    exponentialEntireValue-injective (logarithmFromEquivalence equivalent value) x
      (expℝ-logarithm equivalent value ∙ sym exponential-value)

  logarithm-one : ∀ equivalent →
    logarithmFromEquivalence equivalent (positiveRat 1₊) ≡ 0ℝ
  logarithm-one equivalent =
    cong (logarithmFromEquivalence equivalent)
      (Σ≡Prop isPropIsPositive
        (positiveRatOneValue ∙ sym exponentialEntireValue-zero
          ∙ sym (expPositive-value 0ℝ)))
      ∙ logarithm-expPositive equivalent 0ℝ

  logarithm-product : ∀ equivalent (left right : ℝ>0) →
    logarithmFromEquivalence equivalent (left ·>0 right) ≡
    logarithmFromEquivalence equivalent left + logarithmFromEquivalence equivalent right
  logarithm-product equivalent left right =
    logarithm-unique equivalent (left ·>0 right)
      (logarithmFromEquivalence equivalent left + logarithmFromEquivalence equivalent right)
      (exponentialEntireValue-add
        (logarithmFromEquivalence equivalent left)
        (logarithmFromEquivalence equivalent right)
        ∙ cong₂ _·_ (expℝ-logarithm equivalent left) (expℝ-logarithm equivalent right))

  logarithm-reciprocal : ∀ equivalent (value : ℝ>0) →
    logarithmFromEquivalence equivalent
      (positiveReciprocal (fst value) (snd value)
        , positiveReciprocalPositive (fst value) (snd value))
      ≡ - logarithmFromEquivalence equivalent value
  logarithm-reciprocal equivalent value =
    additiveInverseFromSumZero (logarithmFromEquivalence equivalent value)
      (logarithmFromEquivalence equivalent inverse)
      (sym (logarithm-product equivalent value inverse)
        ∙ cong (logarithmFromEquivalence equivalent)
            (Σ≡Prop isPropIsPositive (positiveReciprocalLaw (fst value) (snd value)))
        ∙ logarithm-one equivalent)
    where
    inverse : ℝ>0
    inverse = positiveReciprocal (fst value) (snd value)
      , positiveReciprocalPositive (fst value) (snd value)

  logarithm-injective : ∀ equivalent (left right : ℝ>0) →
    logarithmFromEquivalence equivalent left ≡ logarithmFromEquivalence equivalent right →
    left ≡ right
  logarithm-injective equivalent left right equal =
    Σ≡Prop isPropIsPositive
      (sym (expℝ-logarithm equivalent left)
        ∙ cong expℝ equal ∙ expℝ-logarithm equivalent right)

  logarithm-preserves≤ : ∀ equivalent (left right : ℝ>0) → fst left ≤ℝ fst right →
    logarithmFromEquivalence equivalent left ≤ℝ logarithmFromEquivalence equivalent right
  logarithm-preserves≤ equivalent left right ordered =
    exponentialEntireValue-reflects≤
      (logarithmFromEquivalence equivalent left) (logarithmFromEquivalence equivalent right)
      (subst2 _≤ℝ_ (sym (expℝ-logarithm equivalent left))
        (sym (expℝ-logarithm equivalent right)) ordered)

  logarithm-reflects≤ : ∀ equivalent (left right : ℝ>0) →
    logarithmFromEquivalence equivalent left ≤ℝ logarithmFromEquivalence equivalent right →
    fst left ≤ℝ fst right
  logarithm-reflects≤ equivalent left right ordered =
    subst2 _≤ℝ_ (expℝ-logarithm equivalent left) (expℝ-logarithm equivalent right)
      (exponentialEntireValue-preserves≤
        (logarithmFromEquivalence equivalent left) (logarithmFromEquivalence equivalent right)
        ordered)

  logarithm-strictlyIncreasing : ∀ equivalent (left right : ℝ>0) → fst left <ℝ fst right →
    logarithmFromEquivalence equivalent left <ℝ logarithmFromEquivalence equivalent right
  logarithm-strictlyIncreasing equivalent left right ordered =
    continuousReflectsStrictOnOrderedInputs expℝ exponentialEntireValueIsContinuous
      (logarithmFromEquivalence equivalent left) (logarithmFromEquivalence equivalent right)
      (logarithm-preserves≤ equivalent left right (<ℝ-weaken (fst left) (fst right) ordered))
      (subst2 _<ℝ_ (sym (expℝ-logarithm equivalent left))
        (sym (expℝ-logarithm equivalent right)) ordered)

  logarithm-reflects< : ∀ equivalent (left right : ℝ>0) →
    logarithmFromEquivalence equivalent left <ℝ logarithmFromEquivalence equivalent right →
    fst left <ℝ fst right
  logarithm-reflects< equivalent left right ordered =
    subst2 _<ℝ_ (expℝ-logarithm equivalent left) (expℝ-logarithm equivalent right)
      (exponentialEntireValue-strictlyIncreasing
        (logarithmFromEquivalence equivalent left) (logarithmFromEquivalence equivalent right)
        ordered)
