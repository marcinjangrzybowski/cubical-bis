module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Addition.Tangent.Product where

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
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Laws
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Addition.Algebra
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Addition.Domain.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Addition.Factorization
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Addition.Tangent.Product.Scale
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Addition.Tangent.Product.Steps


opaque
  tangentAdditionMultipliedEquality :
    (left right : TangentDomain) →
    (sum-apart : 0ℝ #ℝ cosℝ (fst left + fst right)) →
    tangentAdditionCommonCosineFactor left right ·
      (tanℝ ((fst left + fst right) , sum-apart) ·
        tangentAdditionDenominator left right)
      ≡
    tangentAdditionCommonCosineFactor left right ·
      tangentAdditionNumerator left right
  tangentAdditionMultipliedEquality left right sum-apart =
    tangentAdditionChain4
      (common · (tanℝ sum-point · denominator))
      (tanℝ sum-point · (common · denominator))
      (tanℝ sum-point · cosℝ (fst left + fst right))
      (sinℝ (fst left + fst right))
      (common · numerator)
      (tangentAdditionRearrangeProduct
        left right sum-apart)
      (tangentAdditionScaledCosineFactorization
        left right sum-apart)
      (tangentAdditionEvaluateTangentCosine
        left right sum-apart)
      (tangentAdditionSineFactorization left right)
    where
    sum-point : TangentDomain
    sum-point = (fst left + fst right) , sum-apart

    common : ℝ
    common = tangentAdditionCommonCosineFactor left right

    denominator : ℝ
    denominator = tangentAdditionDenominator left right

    numerator : ℝ
    numerator = tangentAdditionNumerator left right
