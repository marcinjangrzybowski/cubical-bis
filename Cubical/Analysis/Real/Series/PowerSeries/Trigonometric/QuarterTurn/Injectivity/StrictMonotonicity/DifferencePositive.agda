module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.StrictMonotonicity.DifferencePositive where

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
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Difference
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Geometry
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.StrictMonotonicity.Factors
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.StrictMonotonicity.Order


opaque
  quarterTurnSineDifferencePositive : ∀ quarter →
    IsPositiveQuarterTurn quarter →
    IsFirstPositiveCosineZero quarter →
    ∀ x y →
    (- quarter) ≤ℝ x → y ≤ℝ quarter → x <ℝ y →
    0ℝ <ℝ sinℝ y + (- sinℝ x)
  quarterTurnSineDifferencePositive
      quarter positive-quarter characterization x y
      negative-quarter≤x y≤quarter x<y =
    positivePathBackward
      (sinℝ y + (- sinℝ x))
      ((cosℝ (quarterTurnMidpoint x y)
          · sinℝ (quarterTurnHalfDifference x y))
        +
       (cosℝ (quarterTurnMidpoint x y)
          · sinℝ (quarterTurnHalfDifference x y)))
      (sinℝ-quarterTurnDifference x y)
      (quarterTurnDifferenceFactorsPositive
        quarter positive-quarter characterization x y
        negative-quarter≤x y≤quarter x<y)
