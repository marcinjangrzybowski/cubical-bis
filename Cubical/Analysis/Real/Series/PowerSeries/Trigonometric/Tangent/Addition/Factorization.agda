module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Addition.Factorization where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Inverse.Signed
open import Cubical.Analysis.Real.Order.Apartness
open import Cubical.Analysis.Real.Order.MultiplicativeApartness
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Addition
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Laws
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Addition.Algebra
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Addition.Domain.Base


opaque
  tangentAdditionCosineFactorization : ∀ left right →
    cosℝ (fst left + fst right)
      ≡
    tangentAdditionCommonCosineFactor left right ·
      tangentAdditionDenominator left right
  tangentAdditionCosineFactorization left right =
      cosℝ-add (fst left) (fst right)
    ∙ tangentAdditionCosineFactor
        (sinℝ (fst left)) (sinℝ (fst right))
        (cosℝ (fst left)) (cosℝ (fst right))
        (tanℝ left) (tanℝ right)
        (cosℝ-mul-tanℝ left)
        (cosℝ-mul-tanℝ right)


  tangentAdditionSineFactorization : ∀ left right →
    sinℝ (fst left + fst right)
      ≡
    tangentAdditionCommonCosineFactor left right ·
      tangentAdditionNumerator left right
  tangentAdditionSineFactorization left right =
      sinℝ-add (fst left) (fst right)
    ∙ tangentAdditionSineFactor
        (sinℝ (fst left)) (sinℝ (fst right))
        (cosℝ (fst left)) (cosℝ (fst right))
        (tanℝ left) (tanℝ right)
        (cosℝ-mul-tanℝ left)
        (cosℝ-mul-tanℝ right)


  tangentAdditionCommonFactorApart : ∀ left right →
    0ℝ #ℝ tangentAdditionCommonCosineFactor left right
  tangentAdditionCommonFactorApart left right =
    apartMul
      (cosℝ (fst left)) (cosℝ (fst right))
      (snd left) (snd right)


  tangentAdditionCosineApartFromProductApart : ∀ left right →
    0ℝ #ℝ
      (tangentAdditionCommonCosineFactor left right ·
        tangentAdditionDenominator left right) →
    0ℝ #ℝ cosℝ (fst left + fst right)
  tangentAdditionCosineApartFromProductApart
      left right product-apart =
    subst
      (0ℝ #ℝ_)
      (sym (tangentAdditionCosineFactorization left right))
      product-apart


  tangentAdditionCosineApartFromDenominatorApart : ∀ left right →
    0ℝ #ℝ tangentAdditionDenominator left right →
    0ℝ #ℝ cosℝ (fst left + fst right)
  tangentAdditionCosineApartFromDenominatorApart
      left right denominator-apart =
    tangentAdditionCosineApartFromProductApart left right
      (apartMul
        (tangentAdditionCommonCosineFactor left right)
        (tangentAdditionDenominator left right)
        (tangentAdditionCommonFactorApart left right)
        denominator-apart)


  tangentAdditionProductApartFromCosineApart : ∀ left right →
    0ℝ #ℝ cosℝ (fst left + fst right) →
    0ℝ #ℝ
      (tangentAdditionCommonCosineFactor left right ·
        tangentAdditionDenominator left right)
  tangentAdditionProductApartFromCosineApart
      left right cosine-apart =
    subst
      (0ℝ #ℝ_)
      (tangentAdditionCosineFactorization left right)
      cosine-apart


  tangentAdditionDenominatorApartFromCosineApart : ∀ left right →
    0ℝ #ℝ cosℝ (fst left + fst right) →
    0ℝ #ℝ tangentAdditionDenominator left right
  tangentAdditionDenominatorApartFromCosineApart
      left right cosine-apart =
    apartMul-reflects-right
      (tangentAdditionCommonCosineFactor left right)
      (tangentAdditionDenominator left right)
      (tangentAdditionCommonFactorApart left right)
      (tangentAdditionProductApartFromCosineApart
        left right cosine-apart)
