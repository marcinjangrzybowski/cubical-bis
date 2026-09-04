module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Addition.Secant.Cleared where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Order.Apartness
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Addition.Algebra
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Addition.Domain.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Addition.Factorization
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Addition.Secant.Product


opaque
  secℝ-add-clearedWith : (left right : TangentDomain) →
    (sum-apart : 0ℝ #ℝ cosℝ (fst left + fst right)) →
    secℝ ((fst left + fst right) , sum-apart) ·
        tangentAdditionDenominator left right
      ≡
    secantAdditionNumerator left right
  secℝ-add-clearedWith left right sum-apart =
    tangentAdditionCancelCommonLeft
      secant-times-denominator numerator common common-apart
      (secantAdditionMultipliedEquality left right sum-apart)
    where
    sum-point : TangentDomain
    sum-point = (fst left + fst right) , sum-apart

    common : ℝ
    common = tangentAdditionCommonCosineFactor left right

    denominator : ℝ
    denominator = tangentAdditionDenominator left right

    numerator : ℝ
    numerator = secantAdditionNumerator left right

    secant-times-denominator : ℝ
    secant-times-denominator = secℝ sum-point · denominator

    common-apart : 0ℝ #ℝ common
    common-apart = tangentAdditionCommonFactorApart left right
