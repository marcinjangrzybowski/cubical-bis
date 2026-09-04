module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.AbsoluteCosine.ContinuityWitness where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Relation.Premetric.Mappings

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire

open CategoryStructures


opaque
  cosineAfterAbsoluteIsContinuous :
    isContinuous
      (ℝPremetricSpace .snd) (cosℝ ∘ absℝ)
      (ℝPremetricSpace .snd)
  cosineAfterAbsoluteIsContinuous =
    snd
      ((cosℝ , cosℝIsContinuous) ∘C
        (absℝ , abs-isContinuous))
