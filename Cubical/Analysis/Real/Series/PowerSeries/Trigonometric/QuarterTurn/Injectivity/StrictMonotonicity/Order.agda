module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.StrictMonotonicity.Order where

open import Cubical.Foundations.Prelude

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Addition


opaque
  positivePathBackward : ∀ (left right : ℝ) →
    left ≡ right → 0ℝ <ℝ right → 0ℝ <ℝ left
  positivePathBackward left right path positive-right =
    subst (0ℝ <ℝ_) (sym path) positive-right


  positiveExplicitDifference→< : ∀ (x y : ℝ) →
    0ℝ <ℝ y + (- x) → x <ℝ y
  positiveExplicitDifference→< x y positive-difference =
    subst2 _<ℝ_
      (addIdL x)
      ( sym (addAssoc y (- x) x)
      ∙ cong (y +_) (addInvL x)
      ∙ addIdR y
      )
      (<ℝ-addR 0ℝ (y + (- x)) x positive-difference)
