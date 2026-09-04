module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Half.Values where

open import Cubical.Foundations.Prelude

open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ)
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Phase


opaque
  sinℝ-halfTurn : ∀ quarter →
    IsPositiveQuarterTurn quarter →
    sinℝ (halfTurn quarter) ≡ 0ℝ
  sinℝ-halfTurn quarter positive-quarter =
      cong sinℝ (halfTurn-equation quarter)
    ∙ sinℝ-add-quarterTurn quarter positive-quarter quarter
    ∙ quarterTurnCosineZero
        {quarter = quarter} positive-quarter


  cosℝ-halfTurn : ∀ quarter →
    IsPositiveQuarterTurn quarter →
    cosℝ (halfTurn quarter) ≡ - 1ℝ
  cosℝ-halfTurn quarter positive-quarter =
      cong cosℝ (halfTurn-equation quarter)
    ∙ cosℝ-add-quarterTurn quarter positive-quarter quarter
    ∙ cong -_
        (quarterTurnSineOne
          {quarter = quarter} positive-quarter)
