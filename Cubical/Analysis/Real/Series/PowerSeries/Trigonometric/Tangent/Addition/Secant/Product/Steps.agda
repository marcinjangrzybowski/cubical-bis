module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Addition.Secant.Product.Steps where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ; mulIdL)
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


opaque
  secantAdditionRearrangeProduct :
    (left right : TangentDomain) →
    (sum-apart : 0ℝ #ℝ cosℝ (fst left + fst right)) →
    tangentAdditionCommonCosineFactor left right ·
      (secℝ ((fst left + fst right) , sum-apart) ·
        tangentAdditionDenominator left right)
      ≡
    secℝ ((fst left + fst right) , sum-apart) ·
      (tangentAdditionCommonCosineFactor left right ·
        tangentAdditionDenominator left right)
  secantAdditionRearrangeProduct left right sum-apart =
    tangentAdditionCommuteCommonFactor
      (tangentAdditionCommonCosineFactor left right)
      (secℝ ((fst left + fst right) , sum-apart))
      (tangentAdditionDenominator left right)


opaque
  secantAdditionScaledCosineFactorization :
    (left right : TangentDomain) →
    (sum-apart : 0ℝ #ℝ cosℝ (fst left + fst right)) →
    secℝ ((fst left + fst right) , sum-apart) ·
      (tangentAdditionCommonCosineFactor left right ·
        tangentAdditionDenominator left right)
      ≡
    secℝ ((fst left + fst right) , sum-apart) ·
      cosℝ (fst left + fst right)
  secantAdditionScaledCosineFactorization
      left right sum-apart =
    tangentAdditionMultiplyPath
      (secℝ ((fst left + fst right) , sum-apart))
      (tangentAdditionCommonCosineFactor left right ·
        tangentAdditionDenominator left right)
      (cosℝ (fst left + fst right))
      (sym (tangentAdditionCosineFactorization left right))


opaque
  secantAdditionEvaluateSecantCosine :
    (left right : TangentDomain) →
    (sum-apart : 0ℝ #ℝ cosℝ (fst left + fst right)) →
    secℝ ((fst left + fst right) , sum-apart) ·
      cosℝ (fst left + fst right)
      ≡ 1ℝ
  secantAdditionEvaluateSecantCosine left right sum-apart =
    secℝ-mul-cosℝ
      ((fst left + fst right) , sum-apart)


opaque
  secantAdditionCommonNumeratorInterchange :
    (left right : TangentDomain) →
    tangentAdditionCommonCosineFactor left right ·
      secantAdditionNumerator left right
      ≡
    (cosℝ (fst left) · secℝ left) ·
      (cosℝ (fst right) · secℝ right)
  secantAdditionCommonNumeratorInterchange left right =
    tangentAdditionInterchange
      (cosℝ (fst left)) (cosℝ (fst right))
      (secℝ left) (secℝ right)


opaque
  secantAdditionCommonNumeratorFactors :
    (left right : TangentDomain) →
    (cosℝ (fst left) · secℝ left) ·
      (cosℝ (fst right) · secℝ right)
      ≡ 1ℝ · 1ℝ
  secantAdditionCommonNumeratorFactors left right =
    cong₂ _·_
      (cosℝ-mul-secℝ left)
      (cosℝ-mul-secℝ right)


opaque
  secantAdditionCommonNumeratorIsOne :
    (left right : TangentDomain) →
    tangentAdditionCommonCosineFactor left right ·
      secantAdditionNumerator left right
      ≡ 1ℝ
  secantAdditionCommonNumeratorIsOne left right =
    tangentAdditionChain3
      (tangentAdditionCommonCosineFactor left right ·
        secantAdditionNumerator left right)
      ((cosℝ (fst left) · secℝ left) ·
        (cosℝ (fst right) · secℝ right))
      (1ℝ · 1ℝ)
      1ℝ
      (secantAdditionCommonNumeratorInterchange left right)
      (secantAdditionCommonNumeratorFactors left right)
      (mulIdL 1ℝ)
