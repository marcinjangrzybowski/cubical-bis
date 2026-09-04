module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Inverse.Endpoints where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Endpoints
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Inverse
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Cosine.Inverse


opaque
  restrictedArcSin-left : ∀ quarter →
    IsPositiveQuarterTurn quarter → 0ℝ ≤ℝ quarter → ∀ equivalent →
    fst (restrictedArcSin quarter equivalent sineUnitLeft) ≡ - quarter
  restrictedArcSin-left quarter positive-quarter nonnegative equivalent =
    cong {x = restrictedArcSin quarter equivalent sineUnitLeft}
      {y = sineQuarterLeft quarter nonnegative} fst
      (restrictedArcSin-unique quarter equivalent sineUnitLeft
        (sineQuarterLeft quarter nonnegative)
        (subst (λ x → sinℝ x ≡ - 1ℝ) (sym coordinate)
          (sinℝ-negativeQuarter quarter positive-quarter)))
    ∙ coordinate
    where
    coordinate : fst (sineQuarterLeft quarter nonnegative) ≡ - quarter
    coordinate = refl

  restrictedArcSin-right : ∀ quarter →
    IsPositiveQuarterTurn quarter → 0ℝ ≤ℝ quarter → ∀ equivalent →
    fst (restrictedArcSin quarter equivalent sineUnitRight) ≡ quarter
  restrictedArcSin-right quarter positive-quarter nonnegative equivalent =
    cong {x = restrictedArcSin quarter equivalent sineUnitRight}
      {y = sineQuarterRight quarter nonnegative} fst
      (restrictedArcSin-unique quarter equivalent sineUnitRight
        (sineQuarterRight quarter nonnegative)
        (subst (λ x → sinℝ x ≡ 1ℝ) (sym coordinate)
          (sinℝ-positiveQuarter quarter positive-quarter)))
    ∙ coordinate
    where
    coordinate : fst (sineQuarterRight quarter nonnegative) ≡ quarter
    coordinate = refl

  restrictedArcCos-left : ∀ quarter →
    IsPositiveQuarterTurn quarter → 0ℝ ≤ℝ quarter → ∀ equivalent →
    fst (restrictedArcCos quarter equivalent sineUnitLeft) ≡ halfTurn quarter
  restrictedArcCos-left quarter positive-quarter nonnegative equivalent =
    restrictedArcCos-value quarter equivalent sineUnitLeft
    ∙ cong (λ x → quarter - x)
        (restrictedArcSin-left quarter positive-quarter nonnegative equivalent)
    ∙ cong (quarter +_) (negInvol quarter)

  restrictedArcCos-right : ∀ quarter →
    IsPositiveQuarterTurn quarter → 0ℝ ≤ℝ quarter → ∀ equivalent →
    fst (restrictedArcCos quarter equivalent sineUnitRight) ≡ 0ℝ
  restrictedArcCos-right quarter positive-quarter nonnegative equivalent =
    restrictedArcCos-value quarter equivalent sineUnitRight
    ∙ cong (λ x → quarter - x)
        (restrictedArcSin-right quarter positive-quarter nonnegative equivalent)
    ∙ subSelf quarter
