module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Inverse.Continuity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Relation.Premetric.Mappings

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ)
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Inverse
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Cosine.Interval
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Cosine.Inverse
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Reflection.Base


-- Radiuswise reflection suffices for continuity.  In particular, this does
-- not select a global modulus or require any countable-choice principle.
opaque
  restrictedArcSinIsContinuous : ∀ quarter equivalent →
    QuarterTurnSineClosenessReflectionModulus quarter →
    isContinuous
      (ClosedIntervalPremetricSpace (- 1ℝ) 1ℝ .snd)
      (restrictedArcSin quarter equivalent)
      (ClosedIntervalPremetricSpace (- quarter) quarter .snd)
  restrictedArcSinIsContinuous quarter equivalent reflection value
      .IsContinuousAt.pres≈ ε =
    PT.map
      (λ (δ , reflects) → δ , λ other close →
        reflects
          (restrictedArcSin quarter equivalent value)
          (restrictedArcSin quarter equivalent other)
          (subst2 (_∼[ δ ]_)
            (sym (sinℝ-restrictedArcSin quarter equivalent value))
            (sym (sinℝ-restrictedArcSin quarter equivalent other)) close))
      (reflection ε)

  restrictedArcCosIsContinuous : ∀ quarter equivalent →
    QuarterTurnSineClosenessReflectionModulus quarter →
    isContinuous
      (ClosedIntervalPremetricSpace (- 1ℝ) 1ℝ .snd)
      (restrictedArcCos quarter equivalent)
      (ClosedIntervalPremetricSpace 0ℝ (halfTurn quarter) .snd)
  restrictedArcCosIsContinuous quarter equivalent reflection value
      .IsContinuousAt.pres≈ ε =
    PT.map
      (λ (δ , preserves) → δ , λ other close →
        subst2 (_∼[ ε ]_)
          (sym (restrictedArcCos-value quarter equivalent value))
          (sym (restrictedArcCos-value quarter equivalent other))
          (add-pres∼₂ quarter _ _ ε
            (neg-isNonExpanding .IsNonExpanding.pres≈ _ _ ε
              (preserves other close))))
      (restrictedArcSinIsContinuous quarter equivalent reflection value
        .IsContinuousAt.pres≈ ε)
