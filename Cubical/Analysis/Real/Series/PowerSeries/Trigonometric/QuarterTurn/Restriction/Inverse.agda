module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Inverse where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Base


-- Every construction of the restricted-sine equivalence uses this same
-- inverse.  No choice principle is needed to invert an existing equivalence.
opaque
  restrictedArcSin : ∀ quarter →
    isEquiv (restrictedSine quarter) →
    SineUnitInterval → SineQuarterInterval quarter
  restrictedArcSin quarter equivalent =
    invEq (restrictedSine quarter , equivalent)

  restrictedSine-arcSin : ∀ quarter equivalent value →
    restrictedSine quarter (restrictedArcSin quarter equivalent value) ≡ value
  restrictedSine-arcSin quarter equivalent =
    secEq (restrictedSine quarter , equivalent)

  restrictedArcSin-sine : ∀ quarter equivalent point →
    restrictedArcSin quarter equivalent (restrictedSine quarter point) ≡ point
  restrictedArcSin-sine quarter equivalent =
    retEq (restrictedSine quarter , equivalent)

  restrictedArcSin-independent : ∀ quarter
    (first second : isEquiv (restrictedSine quarter)) value →
    restrictedArcSin quarter first value ≡
    restrictedArcSin quarter second value
  restrictedArcSin-independent quarter first second value =
    cong (λ equivalent → restrictedArcSin quarter equivalent value)
      (isPropIsEquiv (restrictedSine quarter) first second)


opaque
  sinℝ-restrictedArcSin : ∀ quarter equivalent value →
    sinℝ (fst (restrictedArcSin quarter equivalent value)) ≡ fst value
  sinℝ-restrictedArcSin quarter equivalent value =
    sym (restrictedSine-value quarter (restrictedArcSin quarter equivalent value))
    ∙ cong fst (restrictedSine-arcSin quarter equivalent value)

  restrictedArcSin-unique : ∀ quarter equivalent value point →
    sinℝ (fst point) ≡ fst value →
    restrictedArcSin quarter equivalent value ≡ point
  restrictedArcSin-unique quarter equivalent value point sine-value =
    cong (restrictedArcSin quarter equivalent)
      (sym (sineUnitInterval≡ (restrictedSine quarter point) value
        (restrictedSine-value quarter point ∙ sine-value)))
    ∙ restrictedArcSin-sine quarter equivalent point
