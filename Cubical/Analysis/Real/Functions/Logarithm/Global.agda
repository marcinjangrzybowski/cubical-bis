module Cubical.Analysis.Real.Functions.Logarithm.Global where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (1₊)
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Positive
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ)
open import Cubical.Analysis.Real.Algebra.Inverse.Positive
open import Cubical.Analysis.Real.Algebra.Inverse.Order
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Domain.OpenInterval
open import Cubical.Analysis.Real.Calculus.Derivative.Base
open import Cubical.Analysis.Real.Functions.Exponential
open import Cubical.Analysis.Real.Functions.Exponential.Inverse
open import Cubical.Analysis.Real.Functions.Logarithm.Base
open import Cubical.Analysis.Real.Functions.Logarithm.Properties
open import Cubical.Analysis.Real.Functions.Logarithm.Continuity
open import Cubical.Analysis.Real.Functions.Logarithm.Derivative
open import Cubical.Analysis.Real.Series.PowerSeries.Exponential.Addition


-- The equivalence is constructed by geometric iteration; callers supply
-- only the positive argument, not an inverse-existence assumption.
opaque
  logℝ : ℝ>0 → ℝ
  logℝ = logarithmFromEquivalence expPositive-isEquiv

  logℝ-value : ∀ value →
    logℝ value ≡ logarithmFromEquivalence expPositive-isEquiv value
  logℝ-value value = refl


opaque
  expPositive-logℝ : ∀ value → expPositive (logℝ value) ≡ value
  expPositive-logℝ value =
    cong expPositive (logℝ-value value)
    ∙ expPositive-logarithm expPositive-isEquiv value

  expℝ-logℝ : ∀ value → expℝ (logℝ value) ≡ fst value
  expℝ-logℝ value =
    cong expℝ (logℝ-value value) ∙ expℝ-logarithm expPositive-isEquiv value

  logℝ-expPositive : ∀ x → logℝ (expPositive x) ≡ x
  logℝ-expPositive x =
    logℝ-value (expPositive x) ∙ logarithm-expPositive expPositive-isEquiv x

  logℝ-unique : ∀ value x → expℝ x ≡ fst value → logℝ value ≡ x
  logℝ-unique value x equation =
    logℝ-value value ∙ logarithm-unique expPositive-isEquiv value x equation

  logℝ-atOne : ∀ value → fst value ≡ 1ℝ → logℝ value ≡ 0ℝ
  logℝ-atOne value equal =
    logℝ-unique value 0ℝ (exponentialEntireValue-zero ∙ sym equal)

  logℝ-product : ∀ left right →
    logℝ (left ·>0 right) ≡ logℝ left + logℝ right
  logℝ-product left right =
    logℝ-value (left ·>0 right) ∙ logarithm-product expPositive-isEquiv left right
    ∙ cong₂ _+_ (sym (logℝ-value left)) (sym (logℝ-value right))

  logℝ-reciprocal : ∀ value →
    logℝ (positiveReciprocal (fst value) (snd value)
      , positiveReciprocalPositive (fst value) (snd value)) ≡ - logℝ value
  logℝ-reciprocal value =
    logℝ-value (positiveReciprocal (fst value) (snd value)
      , positiveReciprocalPositive (fst value) (snd value))
    ∙ logarithm-reciprocal expPositive-isEquiv value
    ∙ cong -_ (sym (logℝ-value value))

  logℝ-injective : ∀ left right → logℝ left ≡ logℝ right → left ≡ right
  logℝ-injective left right equal =
    logarithm-injective expPositive-isEquiv left right
      (sym (logℝ-value left) ∙ equal ∙ logℝ-value right)

  logℝ-preserves≤ : ∀ left right → fst left ≤ℝ fst right →
    logℝ left ≤ℝ logℝ right
  logℝ-preserves≤ left right ordered =
    subst2 _≤ℝ_ (sym (logℝ-value left)) (sym (logℝ-value right))
      (logarithm-preserves≤ expPositive-isEquiv left right ordered)

  logℝ-reflects≤ : ∀ left right → logℝ left ≤ℝ logℝ right →
    fst left ≤ℝ fst right
  logℝ-reflects≤ left right ordered =
    logarithm-reflects≤ expPositive-isEquiv left right
      (subst2 _≤ℝ_ (logℝ-value left) (logℝ-value right) ordered)

  logℝ-strictlyIncreasing : ∀ left right → fst left <ℝ fst right →
    logℝ left <ℝ logℝ right
  logℝ-strictlyIncreasing left right ordered =
    subst2 _<ℝ_ (sym (logℝ-value left)) (sym (logℝ-value right))
      (logarithm-strictlyIncreasing expPositive-isEquiv left right ordered)

  logℝ-reflects< : ∀ left right → logℝ left <ℝ logℝ right →
    fst left <ℝ fst right
  logℝ-reflects< left right ordered =
    logarithm-reflects< expPositive-isEquiv left right
      (subst2 _<ℝ_ (logℝ-value left) (logℝ-value right) ordered)

  logℝ-isContinuous :
    isContinuous (LowerOpenHalfLinePremetricSpace 0ℝ .snd) logℝ
      (ℝPremetricSpace .snd)
  logℝ-isContinuous =
    subst (λ function → isContinuous (LowerOpenHalfLinePremetricSpace 0ℝ .snd)
      function (ℝPremetricSpace .snd)) (sym (funExt logℝ-value))
      (logarithmFromEquivalenceIsContinuous expPositive-isEquiv)

  logℝ-hasDerivative :
    IsDerivativeAlong (LowerOpenHalfLinePremetricSpace 0ℝ .snd) fst
      logℝ logarithmDerivative
  logℝ-hasDerivative =
    subst (λ function → IsDerivativeAlong
      (LowerOpenHalfLinePremetricSpace 0ℝ .snd) fst function logarithmDerivative)
      (sym (funExt logℝ-value)) (logarithmHasDerivative expPositive-isEquiv)


logPositiveEquiv : ℝ>0 ≃ ℝ
logPositiveEquiv =
  isoToEquiv (iso logℝ expPositive logℝ-expPositive expPositive-logℝ)
