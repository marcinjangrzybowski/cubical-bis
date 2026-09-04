module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Difference.Formula where

open import Cubical.Foundations.Prelude

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.Multiplication
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Addition
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Difference.Algebra
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Difference.MinusAddition
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Difference.Parity


opaque
  sinℝ-symmetricDifference : ∀ (midpoint difference : ℝ) →
    sinℝ (midpoint + difference)
      + (- sinℝ (midpoint + (- difference)))
      ≡
    (cosℝ midpoint · sinℝ difference)
    + (cosℝ midpoint · sinℝ difference)
  sinℝ-symmetricDifference midpoint difference =
    cong₂ _+_
      (sinℝ-add midpoint difference)
      (cong -_
        (sinℝ-midpointMinusAddition midpoint difference
        ∙ sineMidpointMinusParity midpoint difference))
    ∙ twiceAfterDifference
        (sinℝ midpoint · cosℝ difference)
        (cosℝ midpoint · sinℝ difference)
