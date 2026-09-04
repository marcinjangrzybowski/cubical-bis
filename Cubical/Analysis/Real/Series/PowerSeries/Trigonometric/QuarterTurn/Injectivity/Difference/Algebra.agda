module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Difference.Algebra where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
import Cubical.Algebra.Ring.Properties as RingProperties

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.CommRing


private
  module ℝRing =
    RingProperties.RingTheory (CommRing→Ring ℝCommRing)


opaque
  twiceAfterDifference : ∀ (a b : ℝ) →
    (a + b) + (- (a + (- b))) ≡ b + b
  twiceAfterDifference a b =
    cong ((a + b) +_)
      (sym (ℝRing.-Dist a (- b)))
    ∙ ℝRing.+ShufflePairs a b (- a) (- (- b))
    ∙ cong₂ _+_
        (addInvR a)
        (cong (b +_) (negInvol b))
    ∙ addIdL (b + b)
