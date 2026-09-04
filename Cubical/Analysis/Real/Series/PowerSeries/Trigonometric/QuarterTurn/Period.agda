module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Period where

open import Cubical.Foundations.Prelude

open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (addAssoc)
open import Cubical.Analysis.Real.Algebra.AdditiveGroup using (negInvol)
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Half


opaque
  sinℝ-add-fullTurn : ∀ quarter →
    IsPositiveQuarterTurn quarter →
    ∀ x → sinℝ (x + fullTurn quarter) ≡ sinℝ x
  sinℝ-add-fullTurn quarter positive-quarter x =
      cong sinℝ
        (cong (x +_) (fullTurn-equation quarter))
    ∙ cong sinℝ
        (addAssoc x (halfTurn quarter) (halfTurn quarter))
    ∙ sinℝ-add-halfTurn
        quarter positive-quarter (x + halfTurn quarter)
    ∙ cong -_
        (sinℝ-add-halfTurn quarter positive-quarter x)
    ∙ negInvol (sinℝ x)


  cosℝ-add-fullTurn : ∀ quarter →
    IsPositiveQuarterTurn quarter →
    ∀ x → cosℝ (x + fullTurn quarter) ≡ cosℝ x
  cosℝ-add-fullTurn quarter positive-quarter x =
      cong cosℝ
        (cong (x +_) (fullTurn-equation quarter))
    ∙ cong cosℝ
        (addAssoc x (halfTurn quarter) (halfTurn quarter))
    ∙ cosℝ-add-halfTurn
        quarter positive-quarter (x + halfTurn quarter)
    ∙ cong -_
        (cosℝ-add-halfTurn quarter positive-quarter x)
    ∙ negInvol (cosℝ x)
