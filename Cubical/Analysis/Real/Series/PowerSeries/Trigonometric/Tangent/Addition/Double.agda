module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Addition.Double where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ)
open import Cubical.Analysis.Real.Algebra.Inverse.Signed
open import Cubical.Analysis.Real.Order.Apartness
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Addition.Tangent


-- The double-angle law is the diagonal specialization on the exact domain
-- where 1 - tan(x)² is apart from zero.

TangentDoubleDomain : Type
TangentDoubleDomain =
  Σ[ point ∈ TangentDomain ]
    0ℝ #ℝ tangentAdditionDenominator point point


tangentDoublePoint : TangentDoubleDomain → TangentDomain
tangentDoublePoint = fst


tangentDoubleAdditionData :
  TangentDoubleDomain → TangentAdditionDomain
tangentDoubleAdditionData double-data =
  tangentAdditionFromDenominatorApart
    (fst double-data) (fst double-data) (snd double-data)


tangentDoubleSumPoint :
  TangentDoubleDomain → TangentDomain
tangentDoubleSumPoint double-data =
  tangentAdditionSumPoint
    (tangentDoubleAdditionData double-data)


tangentDoubleDenominatorApart : ∀ double-data →
  0ℝ #ℝ
    tangentAdditionDenominator
      (tangentDoublePoint double-data)
      (tangentDoublePoint double-data)
tangentDoubleDenominatorApart double-data =
  tangentAdditionDenominatorApart
    (tangentDoubleAdditionData double-data)


opaque
  tanℝ-double : ∀ double-data →
    tanℝ (tangentDoubleSumPoint double-data)
      ≡
    divideℝ
      (tanℝ (tangentDoublePoint double-data) +
        tanℝ (tangentDoublePoint double-data))
      (1ℝ -
        (tanℝ (tangentDoublePoint double-data) ·
          tanℝ (tangentDoublePoint double-data)))
      (tangentDoubleDenominatorApart double-data)
  tanℝ-double double-data =
    tanℝ-add (tangentDoubleAdditionData double-data)
