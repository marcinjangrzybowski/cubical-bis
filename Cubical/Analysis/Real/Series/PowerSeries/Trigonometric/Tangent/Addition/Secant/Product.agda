module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Addition.Secant.Product where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ)
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
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Addition.Secant.Product.Steps


opaque
  secantAdditionMultipliedEquality :
    (left right : TangentDomain) →
    (sum-apart : 0ℝ #ℝ cosℝ (fst left + fst right)) →
    tangentAdditionCommonCosineFactor left right ·
      (secℝ ((fst left + fst right) , sum-apart) ·
        tangentAdditionDenominator left right)
      ≡
    tangentAdditionCommonCosineFactor left right ·
      secantAdditionNumerator left right
  secantAdditionMultipliedEquality left right sum-apart =
    tangentAdditionChain4
      (common · (secℝ sum-point · denominator))
      (secℝ sum-point · (common · denominator))
      (secℝ sum-point · cosℝ (fst left + fst right))
      1ℝ
      (common · numerator)
      (secantAdditionRearrangeProduct
        left right sum-apart)
      (secantAdditionScaledCosineFactorization
        left right sum-apart)
      (secantAdditionEvaluateSecantCosine
        left right sum-apart)
      (sym (secantAdditionCommonNumeratorIsOne left right))
    where
    sum-point : TangentDomain
    sum-point = (fst left + fst right) , sum-apart

    common : ℝ
    common = tangentAdditionCommonCosineFactor left right

    denominator : ℝ
    denominator = tangentAdditionDenominator left right

    numerator : ℝ
    numerator = secantAdditionNumerator left right
