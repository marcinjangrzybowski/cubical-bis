module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.StrictMonotonicity.SineFactor where

open import Cubical.Foundations.Prelude

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
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
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Bounds
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.SinePositive


opaque
  quarterTurnHalfDifferenceSinePositive : ∀ quarter →
    IsPositiveQuarterTurn quarter →
    IsFirstPositiveCosineZero quarter →
    ∀ x y →
    (- quarter) ≤ℝ x → y ≤ℝ quarter → x <ℝ y →
    0ℝ <ℝ sinℝ (quarterTurnHalfDifference x y)
  quarterTurnHalfDifferenceSinePositive
      quarter positive-quarter characterization x y
      negative-quarter≤x y≤quarter x<y =
    characterizedSine-positive-to-quarter
      quarter positive-quarter characterization
      (quarterTurnHalfDifference x y)
      (quarterTurnHalfDifference-positive x y x<y)
      (quarterTurnHalfDifference≤quarter quarter x y
        negative-quarter≤x y≤quarter)
