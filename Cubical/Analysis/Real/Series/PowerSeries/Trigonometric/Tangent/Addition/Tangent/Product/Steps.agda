module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Addition.Tangent.Product.Steps where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

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


opaque
  tangentAdditionRearrangeProduct :
    (left right : TangentDomain) →
    (sum-apart : 0ℝ #ℝ cosℝ (fst left + fst right)) →
    tangentAdditionCommonCosineFactor left right ·
      (tanℝ ((fst left + fst right) , sum-apart) ·
        tangentAdditionDenominator left right)
      ≡
    tanℝ ((fst left + fst right) , sum-apart) ·
      (tangentAdditionCommonCosineFactor left right ·
        tangentAdditionDenominator left right)
  tangentAdditionRearrangeProduct left right sum-apart =
    tangentAdditionCommuteCommonFactor
      (tangentAdditionCommonCosineFactor left right)
      (tanℝ ((fst left + fst right) , sum-apart))
      (tangentAdditionDenominator left right)


  tangentAdditionEvaluateTangentCosine :
    (left right : TangentDomain) →
    (sum-apart : 0ℝ #ℝ cosℝ (fst left + fst right)) →
    tanℝ ((fst left + fst right) , sum-apart) ·
      cosℝ (fst left + fst right)
      ≡
    sinℝ (fst left + fst right)
  tangentAdditionEvaluateTangentCosine left right sum-apart =
    tanℝ-mul-cosℝ
      ((fst left + fst right) , sum-apart)
