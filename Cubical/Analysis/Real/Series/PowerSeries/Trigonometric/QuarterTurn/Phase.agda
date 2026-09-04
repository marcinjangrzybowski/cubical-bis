module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Phase where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
import Cubical.Algebra.Ring.Properties as RingProperties

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Addition
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Base


private
  module ℝRing =
    RingProperties.RingTheory (CommRing→Ring ℝCommRing)


opaque
  sinℝ-add-quarterTurn : ∀ quarter →
    IsPositiveQuarterTurn quarter →
    ∀ x → sinℝ (x + quarter) ≡ cosℝ x
  sinℝ-add-quarterTurn quarter positive-quarter x =
      sinℝ-add x quarter
    ∙ cong₂ _+_
        (cong (sinℝ x ·_)
          (quarterTurnCosineZero positive-quarter))
        (cong (cosℝ x ·_)
          (quarterTurnSineOne positive-quarter))
    ∙ cong₂ _+_
        (ℝRing.0RightAnnihilates (sinℝ x))
        (mulIdR (cosℝ x))
    ∙ addIdL (cosℝ x)


  cosℝ-add-quarterTurn : ∀ quarter →
    IsPositiveQuarterTurn quarter →
    ∀ x → cosℝ (x + quarter) ≡ - sinℝ x
  cosℝ-add-quarterTurn quarter positive-quarter x =
      cosℝ-add x quarter
    ∙ cong₂ _-_
        (cong (cosℝ x ·_)
          (quarterTurnCosineZero positive-quarter))
        (cong (sinℝ x ·_)
          (quarterTurnSineOne positive-quarter))
    ∙ cong₂ _-_
        (ℝRing.0RightAnnihilates (cosℝ x))
        (mulIdR (sinℝ x))
    ∙ zeroSub (sinℝ x)
