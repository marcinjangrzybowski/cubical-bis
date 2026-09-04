module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Cosine.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (addComm)
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ)
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.SharpBounds
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Phase
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Cosine.Interval


opaque
  restrictedCosine : ∀ quarter → CosineHalfInterval quarter → SineUnitInterval
  restrictedCosine quarter point =
    symmetricIntervalFromAbsBound 1ℝ (cosℝ (fst point))
      (cosℝ-abs≤one (fst point))

  restrictedCosine-value : ∀ quarter point →
    fst (restrictedCosine quarter point) ≡ cosℝ (fst point)
  restrictedCosine-value quarter point = refl


opaque
  sinℝ-quarterReflection : ∀ quarter → IsPositiveQuarterTurn quarter →
    ∀ x → sinℝ (quarter + (- x)) ≡ cosℝ x
  sinℝ-quarterReflection quarter positive-quarter x =
    cong sinℝ (addComm quarter (- x))
    ∙ sinℝ-add-quarterTurn quarter positive-quarter (- x)
    ∙ cosℝ-neg x

  restrictedCosine-asSine : ∀ quarter → IsPositiveQuarterTurn quarter →
    ∀ point →
    restrictedCosine quarter point ≡
    restrictedSine quarter (cosineToSineInterval quarter point)
  restrictedCosine-asSine quarter positive-quarter point =
    sineUnitInterval≡ (restrictedCosine quarter point)
      (restrictedSine quarter (cosineToSineInterval quarter point))
      (restrictedCosine-value quarter point
      ∙ sym reflected-sine
      ∙ sym (restrictedSine-value quarter (cosineToSineInterval quarter point)))
    where
    reflected-sine :
      sinℝ (fst (cosineToSineInterval quarter point)) ≡ cosℝ (fst point)
    reflected-sine =
      subst (λ x → sinℝ x ≡ cosℝ (fst point))
        (sym (cosineToSineInterval-value quarter point))
        (sinℝ-quarterReflection quarter positive-quarter (fst point))


restrictedCosine-isEquivFromSine : ∀ quarter →
  IsPositiveQuarterTurn quarter →
  isEquiv (restrictedSine quarter) → isEquiv (restrictedCosine quarter)
restrictedCosine-isEquivFromSine quarter positive-quarter sine-equivalent =
  subst isEquiv
    (sym (funExt (restrictedCosine-asSine quarter positive-quarter)))
    (snd (compEquiv (cosineSineIntervalEquiv quarter)
      (restrictedSine quarter , sine-equivalent)))


restrictedCosineEquivFromSine : ∀ quarter →
  IsPositiveQuarterTurn quarter →
  isEquiv (restrictedSine quarter) →
  CosineHalfInterval quarter ≃ SineUnitInterval
restrictedCosineEquivFromSine quarter positive-quarter sine-equivalent =
  restrictedCosine quarter
  , restrictedCosine-isEquivFromSine quarter positive-quarter sine-equivalent
