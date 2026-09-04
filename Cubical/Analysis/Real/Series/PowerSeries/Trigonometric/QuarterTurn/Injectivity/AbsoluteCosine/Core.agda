module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.AbsoluteCosine.Core where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Extensionality
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.AbsoluteCosine.Rational
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.AbsoluteCosine.ContinuityWitness


opaque
  cosℝ-absolute : ∀ x →
    cosℝ (absℝ x) ≡ cosℝ x
  cosℝ-absolute = funExt⁻
    (continuousExtensionality
      (cosℝ ∘ absℝ) cosℝ
      cosineAfterAbsoluteIsContinuous
      cosℝIsContinuous
      cosine-absolute-rational)
