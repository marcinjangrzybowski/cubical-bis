module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Addition.Tangent where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Inverse.Signed
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Addition.Domain public
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Addition.Tangent.Core


opaque
  tanℝ-add-cleared : ∀ addition-data →
    tanℝ (tangentAdditionSumPoint addition-data) ·
        tangentAdditionDenominator
          (tangentAdditionLeft addition-data)
          (tangentAdditionRight addition-data)
      ≡
    tangentAdditionNumerator
      (tangentAdditionLeft addition-data)
      (tangentAdditionRight addition-data)
  tanℝ-add-cleared addition-data =
    tanℝ-add-clearedWith
      (fst (fst addition-data))
      (snd (fst addition-data))
      (snd addition-data)


  tanℝ-add : ∀ addition-data →
    tanℝ (tangentAdditionSumPoint addition-data)
      ≡
    divideℝ
      (tangentAdditionNumerator
        (tangentAdditionLeft addition-data)
        (tangentAdditionRight addition-data))
      (tangentAdditionDenominator
        (tangentAdditionLeft addition-data)
        (tangentAdditionRight addition-data))
      (tangentAdditionDenominatorApart addition-data)
  tanℝ-add addition-data =
    tanℝ-addWith
      (fst (fst addition-data))
      (snd (fst addition-data))
      (snd addition-data)
      (tangentAdditionDenominatorApart addition-data)
