module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.StrictMonotonicity where

open import Cubical.Foundations.Prelude
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Order.Strict.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Characterization
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Restriction.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.StrictMonotonicity.DifferencePositive
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.StrictMonotonicity.Order


opaque
  sinℝ-strictMonotone-on-quarterInterval : ∀ quarter →
    IsPositiveQuarterTurn quarter →
    IsFirstPositiveCosineZero quarter →
    ∀ (left right : SineQuarterInterval quarter) →
    fst left <ℝ fst right →
    sinℝ (fst left) <ℝ sinℝ (fst right)
  sinℝ-strictMonotone-on-quarterInterval
      quarter positive-quarter characterization left right left<right =
    positiveExplicitDifference→<
      (sinℝ (fst left)) (sinℝ (fst right))
      (quarterTurnSineDifferencePositive
        quarter positive-quarter characterization
        (fst left) (fst right)
        (fst (snd left)) (snd (snd right)) left<right)
