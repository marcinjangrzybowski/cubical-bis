module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Existence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Characterization
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Iteration
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Equivalence
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Cosine.Interval
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Cosine.Base

-- Exact closed-interval equivalences. The intermediate-value witness is
-- constructed by the arithmetic iteration, rather than supplied by callers.
opaque
  restrictedSine-isEquiv : ∀ quarter →
    IsPositiveQuarterTurn quarter → IsFirstPositiveCosineZero quarter →
    isEquiv (restrictedSine quarter)
  restrictedSine-isEquiv quarter turn first =
    restrictedSine-isEquivFromIntermediateValue quarter turn first
      (sineQuarterIntermediateValueByIteration quarter turn first)

  restrictedCosine-isEquiv : ∀ quarter →
    IsPositiveQuarterTurn quarter → IsFirstPositiveCosineZero quarter →
    isEquiv (restrictedCosine quarter)
  restrictedCosine-isEquiv quarter turn first =
    restrictedCosine-isEquivFromSine quarter turn (restrictedSine-isEquiv quarter turn first)

restrictedSineEquiv : ∀ quarter →
  IsPositiveQuarterTurn quarter → IsFirstPositiveCosineZero quarter →
  SineQuarterInterval quarter ≃ SineUnitInterval
restrictedSineEquiv quarter turn first =
  restrictedSine quarter , restrictedSine-isEquiv quarter turn first

restrictedCosineEquiv : ∀ quarter →
  IsPositiveQuarterTurn quarter → IsFirstPositiveCosineZero quarter →
  CosineHalfInterval quarter ≃ SineUnitInterval
restrictedCosineEquiv quarter turn first =
  restrictedCosine quarter , restrictedCosine-isEquiv quarter turn first
