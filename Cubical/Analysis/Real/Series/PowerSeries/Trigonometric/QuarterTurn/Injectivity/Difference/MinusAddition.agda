module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Difference.MinusAddition where

open import Cubical.Foundations.Prelude

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Addition


opaque
  sinℝ-midpointMinusAddition : ∀ (midpoint difference : ℝ) →
    sinℝ (midpoint + (- difference))
      ≡
    (sinℝ midpoint · cosℝ (- difference))
      + (cosℝ midpoint · sinℝ (- difference))
  sinℝ-midpointMinusAddition midpoint difference =
    sinℝ-add midpoint (- difference)
