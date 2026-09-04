module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Addition.Secant where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Inverse.Signed
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Addition.Domain public
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Addition.Secant.Core


opaque
  secℝ-add-cleared : ∀ addition-data →
    secℝ (tangentAdditionSumPoint addition-data) ·
        tangentAdditionDenominator
          (tangentAdditionLeft addition-data)
          (tangentAdditionRight addition-data)
      ≡
    secantAdditionNumerator
      (tangentAdditionLeft addition-data)
      (tangentAdditionRight addition-data)
  secℝ-add-cleared addition-data =
    secℝ-add-clearedWith
      (fst (fst addition-data))
      (snd (fst addition-data))
      (snd addition-data)


  secℝ-add : ∀ addition-data →
    secℝ (tangentAdditionSumPoint addition-data)
      ≡
    divideℝ
      (secantAdditionNumerator
        (tangentAdditionLeft addition-data)
        (tangentAdditionRight addition-data))
      (tangentAdditionDenominator
        (tangentAdditionLeft addition-data)
        (tangentAdditionRight addition-data))
      (tangentAdditionDenominatorApart addition-data)
  secℝ-add addition-data =
    secℝ-addWith
      (fst (fst addition-data))
      (snd (fst addition-data))
      (snd addition-data)
      (tangentAdditionDenominatorApart addition-data)
