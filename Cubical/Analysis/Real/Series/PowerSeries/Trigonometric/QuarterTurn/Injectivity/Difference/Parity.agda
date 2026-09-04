module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Difference.Parity where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
import Cubical.Algebra.Ring.Properties as RingProperties

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire


private
  module ℝRing =
    RingProperties.RingTheory (CommRing→Ring ℝCommRing)


opaque
  sineMidpointMinusParity : ∀ (midpoint difference : ℝ) →
    (sinℝ midpoint · cosℝ (- difference))
      + (cosℝ midpoint · sinℝ (- difference))
      ≡
    (sinℝ midpoint · cosℝ difference)
      + (- (cosℝ midpoint · sinℝ difference))
  sineMidpointMinusParity midpoint difference =
    cong₂ _+_
      (cong (sinℝ midpoint ·_) (cosℝ-neg difference))
      (cong (cosℝ midpoint ·_) (sinℝ-neg difference))
    ∙ cong ((sinℝ midpoint · cosℝ difference) +_)
        (ℝRing.-DistR·
          (cosℝ midpoint) (sinℝ difference))
