module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Addition where

open import Cubical.Foundations.Prelude

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Coefficients
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire

open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Addition.Signs public
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Addition.Algebra public
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Addition.DividedPowers public
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Addition.Summands public
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Addition.HasSum public
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Addition.Finite public


sineAddHasAdditionSum : ∀ x y →
  HasSum
    (powerSeriesTerms sineCoefficients (x + y))
    ((sinℝ x · cosℝ y) + (cosℝ x · sinℝ y))
sineAddHasAdditionSum x y =
  sineAddHasAdditionSumFromConvolution x y
    (sineAdditionConvolutionTerms-sequence x y)


cosineAddHasAdditionSum : ∀ x y →
  HasSum
    (powerSeriesTerms cosineCoefficients (x + y))
    ((cosℝ x · cosℝ y) - (sinℝ x · sinℝ y))
cosineAddHasAdditionSum x y =
  cosineAddHasAdditionSumFromConvolution x y
    (cosineAdditionConvolutionTerms-sequence x y)


opaque
  sinℝ-add : ∀ x y →
    sinℝ (x + y)
      ≡ (sinℝ x · cosℝ y) + (cosℝ x · sinℝ y)
  sinℝ-add x y =
    sinℝ-add-from-convolution x y
      (sineAdditionConvolutionTerms-sequence x y)


  cosℝ-add : ∀ x y →
    cosℝ (x + y)
      ≡ (cosℝ x · cosℝ y) - (sinℝ x · sinℝ y)
  cosℝ-add x y =
    cosℝ-add-from-convolution x y
      (cosineAdditionConvolutionTerms-sequence x y)
