module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.StrictMonotonicity.Factors where

open import Cubical.Foundations.Prelude
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Characterization
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Geometry
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.StrictMonotonicity.CosineFactor
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.StrictMonotonicity.SineFactor
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.StrictMonotonicity.PositiveProduct


opaque
  quarterTurnDifferenceFactorsPositive : ∀ quarter →
    IsPositiveQuarterTurn quarter →
    IsFirstPositiveCosineZero quarter →
    ∀ x y →
    (- quarter) ≤ℝ x → y ≤ℝ quarter → x <ℝ y →
    0ℝ <ℝ
      (cosℝ (quarterTurnMidpoint x y)
        · sinℝ (quarterTurnHalfDifference x y))
      +
      (cosℝ (quarterTurnMidpoint x y)
        · sinℝ (quarterTurnHalfDifference x y))
  quarterTurnDifferenceFactorsPositive
      quarter positive-quarter characterization x y
      negative-quarter≤x y≤quarter x<y =
    positiveProductTwice
      (cosℝ (quarterTurnMidpoint x y))
      (sinℝ (quarterTurnHalfDifference x y))
      (quarterTurnMidpointCosinePositive
        quarter x y characterization
        negative-quarter≤x y≤quarter x<y)
      (quarterTurnHalfDifferenceSinePositive
        quarter positive-quarter characterization x y
        negative-quarter≤x y≤quarter x<y)
