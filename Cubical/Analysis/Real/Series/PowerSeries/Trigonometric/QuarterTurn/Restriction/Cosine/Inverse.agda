module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Cosine.Inverse where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Inverse
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Cosine.Interval
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Cosine.Base


-- The cosine inverse shares the sine inverse and its equivalence witness:
-- arccos y = quarter - arcsin y, with values in [0, halfTurn quarter].
opaque
  restrictedArcCos : ∀ quarter →
    isEquiv (restrictedSine quarter) →
    SineUnitInterval → CosineHalfInterval quarter
  restrictedArcCos quarter equivalent value =
    sineToCosineInterval quarter (restrictedArcSin quarter equivalent value)

  restrictedArcCos-value : ∀ quarter equivalent value →
    fst (restrictedArcCos quarter equivalent value) ≡
    quarter - fst (restrictedArcSin quarter equivalent value)
  restrictedArcCos-value quarter equivalent value =
    sineToCosineInterval-value quarter (restrictedArcSin quarter equivalent value)

  restrictedCosine-arcCos : ∀ quarter →
    IsPositiveQuarterTurn quarter → ∀ equivalent value →
    restrictedCosine quarter (restrictedArcCos quarter equivalent value) ≡ value
  restrictedCosine-arcCos quarter positive-quarter equivalent value =
    restrictedCosine-asSine quarter positive-quarter
      (sineToCosineInterval quarter (restrictedArcSin quarter equivalent value))
    ∙ cong (restrictedSine quarter)
        (cosineToSine-sineToCosine quarter
          (restrictedArcSin quarter equivalent value))
    ∙ restrictedSine-arcSin quarter equivalent value

  restrictedArcCos-cosine : ∀ quarter →
    IsPositiveQuarterTurn quarter → ∀ equivalent point →
    restrictedArcCos quarter equivalent (restrictedCosine quarter point) ≡ point
  restrictedArcCos-cosine quarter positive-quarter equivalent point =
    cong (λ value → sineToCosineInterval quarter
      (restrictedArcSin quarter equivalent value))
      (restrictedCosine-asSine quarter positive-quarter point)
    ∙ cong (sineToCosineInterval quarter)
        (restrictedArcSin-sine quarter equivalent
          (cosineToSineInterval quarter point))
    ∙ sineToCosine-cosineToSine quarter point

  restrictedArcCos-independent : ∀ quarter
    (first second : isEquiv (restrictedSine quarter)) value →
    restrictedArcCos quarter first value ≡ restrictedArcCos quarter second value
  restrictedArcCos-independent quarter first second value =
    cong (sineToCosineInterval quarter)
      (restrictedArcSin-independent quarter first second value)


opaque
  cosℝ-restrictedArcCos : ∀ quarter →
    IsPositiveQuarterTurn quarter → ∀ equivalent value →
    cosℝ (fst (restrictedArcCos quarter equivalent value)) ≡ fst value
  cosℝ-restrictedArcCos quarter positive-quarter equivalent value =
    sym (restrictedCosine-value quarter (restrictedArcCos quarter equivalent value))
    ∙ cong fst (restrictedCosine-arcCos quarter positive-quarter equivalent value)

  restrictedArcCos-unique : ∀ quarter →
    IsPositiveQuarterTurn quarter → ∀ equivalent value point →
    cosℝ (fst point) ≡ fst value →
    restrictedArcCos quarter equivalent value ≡ point
  restrictedArcCos-unique quarter positive-quarter equivalent value point cosine-value =
    cong (restrictedArcCos quarter equivalent)
      (sym (sineUnitInterval≡ (restrictedCosine quarter point) value
        (restrictedCosine-value quarter point ∙ cosine-value)))
    ∙ restrictedArcCos-cosine quarter positive-quarter equivalent point
