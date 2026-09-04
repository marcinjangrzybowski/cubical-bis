module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Phase where

open import Cubical.Foundations.Prelude

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Phase
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.AbsoluteCosine.Core
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Geometry


opaque
  quarterTurnMidpointCosine-asSineRemainder : ∀ quarter →
    IsPositiveQuarterTurn quarter →
    ∀ x y →
    cosℝ (quarterTurnMidpoint x y)
      ≡
    sinℝ
      (quarter + (- absℝ (quarterTurnMidpoint x y)))
  quarterTurnMidpointCosine-asSineRemainder
      quarter positive-quarter x y =
    sym (cosℝ-absolute (quarterTurnMidpoint x y))
    ∙ sym (cosℝ-neg (absℝ (quarterTurnMidpoint x y)))
    ∙ sym
        (sinℝ-add-quarterTurn quarter positive-quarter
          (- absℝ (quarterTurnMidpoint x y)))
    ∙ cong sinℝ
        (addComm
          (- absℝ (quarterTurnMidpoint x y))
          quarter)
