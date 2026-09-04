module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Continuity where

open import Cubical.Foundations.Prelude

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Premetric.Mappings

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ)
open import Cubical.Analysis.Real.Domain.Interval
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Base


opaque
  restrictedSineIsContinuous : ∀ quarter →
    isContinuous
      (ClosedIntervalPremetricSpace (- quarter) quarter .snd)
      (restrictedSine quarter)
      (ClosedIntervalPremetricSpace (- 1ℝ) 1ℝ .snd)
  restrictedSineIsContinuous quarter point
      .IsContinuousAt.pres≈ ε =
    PT.map
      (λ (delta , preserves) →
        delta , λ other close →
          subst2 (_∼[ ε ]_)
            (sym (restrictedSine-value quarter point))
            (sym (restrictedSine-value quarter other))
            (preserves (fst other) close))
      (sinℝIsContinuous (fst point)
        .IsContinuousAt.pres≈ ε)


restrictedSineContinuous : ∀ quarter →
  C[ ClosedIntervalPremetricSpace (- quarter) quarter
   , ClosedIntervalPremetricSpace (- 1ℝ) 1ℝ ]
restrictedSineContinuous quarter =
  restrictedSine quarter , restrictedSineIsContinuous quarter
