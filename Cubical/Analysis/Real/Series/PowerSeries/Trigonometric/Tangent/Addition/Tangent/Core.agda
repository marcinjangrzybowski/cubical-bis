module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Addition.Tangent.Core where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.Inverse.Signed
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
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Addition.Tangent.Cleared public


opaque
  tanℝ-addWith : (left right : TangentDomain) →
    (sum-apart : 0ℝ #ℝ cosℝ (fst left + fst right)) →
    (denominator-apart :
      0ℝ #ℝ tangentAdditionDenominator left right) →
    tanℝ ((fst left + fst right) , sum-apart)
      ≡
    divideℝ
      (tangentAdditionNumerator left right)
      (tangentAdditionDenominator left right)
      denominator-apart
  tanℝ-addWith left right sum-apart denominator-apart =
    tangentAdditionCancelCommonRight
      (tanℝ sum-point)
      (divideℝ numerator denominator denominator-apart)
      denominator denominator-apart
      ( tanℝ-add-clearedWith left right sum-apart
      ∙ sym
          (mulDivideRight
            numerator denominator denominator-apart)
      )
    where
    sum-point : TangentDomain
    sum-point = (fst left + fst right) , sum-apart

    numerator : ℝ
    numerator = tangentAdditionNumerator left right

    denominator : ℝ
    denominator = tangentAdditionDenominator left right
