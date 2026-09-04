module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Half.Shift where

open import Cubical.Foundations.Prelude

open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (addAssoc)
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Phase


opaque
  sinℝ-add-halfTurn : ∀ quarter →
    IsPositiveQuarterTurn quarter →
    ∀ x → sinℝ (x + halfTurn quarter) ≡ - sinℝ x
  sinℝ-add-halfTurn quarter positive-quarter x =
      cong sinℝ
        (cong (x +_) (halfTurn-equation quarter))
    ∙ cong sinℝ (addAssoc x quarter quarter)
    ∙ sinℝ-add-quarterTurn
        quarter positive-quarter (x + quarter)
    ∙ cosℝ-add-quarterTurn quarter positive-quarter x


  cosℝ-add-halfTurn : ∀ quarter →
    IsPositiveQuarterTurn quarter →
    ∀ x → cosℝ (x + halfTurn quarter) ≡ - cosℝ x
  cosℝ-add-halfTurn quarter positive-quarter x =
      cong cosℝ
        (cong (x +_) (halfTurn-equation quarter))
    ∙ cong cosℝ (addAssoc x quarter quarter)
    ∙ cosℝ-add-quarterTurn
        quarter positive-quarter (x + quarter)
    ∙ cong -_
        (sinℝ-add-quarterTurn quarter positive-quarter x)
