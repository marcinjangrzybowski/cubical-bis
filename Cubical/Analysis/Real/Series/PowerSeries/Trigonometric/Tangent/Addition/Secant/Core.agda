module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Addition.Secant.Core where

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
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Addition.Secant.Cleared public


opaque
  secℝ-addWith : (left right : TangentDomain) →
    (sum-apart : 0ℝ #ℝ cosℝ (fst left + fst right)) →
    (denominator-apart :
      0ℝ #ℝ tangentAdditionDenominator left right) →
    secℝ ((fst left + fst right) , sum-apart)
      ≡
    divideℝ
      (secantAdditionNumerator left right)
      (tangentAdditionDenominator left right)
      denominator-apart
  secℝ-addWith left right sum-apart denominator-apart =
    tangentAdditionCancelCommonRight
      (secℝ sum-point)
      (divideℝ numerator denominator denominator-apart)
      denominator denominator-apart
      ( secℝ-add-clearedWith left right sum-apart
      ∙ sym
          (mulDivideRight
            numerator denominator denominator-apart)
      )
    where
    sum-point : TangentDomain
    sum-point = (fst left + fst right) , sum-apart

    numerator : ℝ
    numerator = secantAdditionNumerator left right

    denominator : ℝ
    denominator = tangentAdditionDenominator left right
