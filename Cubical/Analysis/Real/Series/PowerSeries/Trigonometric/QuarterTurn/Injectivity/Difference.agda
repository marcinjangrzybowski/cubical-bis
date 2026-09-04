module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Difference where

open import Cubical.Foundations.Prelude

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.Multiplication
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Geometry
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Difference.Formula


opaque
  sinℝ-quarterTurnDifference : ∀ (x y : ℝ) →
    sinℝ y + (- sinℝ x)
      ≡
    (cosℝ (quarterTurnMidpoint x y)
      · sinℝ (quarterTurnHalfDifference x y))
    +
    (cosℝ (quarterTurnMidpoint x y)
      · sinℝ (quarterTurnHalfDifference x y))
  sinℝ-quarterTurnDifference x y =
    cong₂ _+_
      (cong sinℝ
        (sym (quarterTurnMidpoint-plusHalfDifference x y)))
      (cong -_
        (cong sinℝ
          (sym
            (quarterTurnMidpoint-plusNegativeHalfDifference x y))))
    ∙ sinℝ-symmetricDifference
        (quarterTurnMidpoint x y)
        (quarterTurnHalfDifference x y)
