module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Addition.Domain.DenominatorApart where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Order.Apartness
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Addition.Domain.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Addition.Factorization


-- A sum-domain point supplies the quotient denominator gap.

opaque
  tangentAdditionDenominatorApart : ∀ addition-data →
    0ℝ #ℝ
      tangentAdditionDenominator
        (tangentAdditionLeft addition-data)
        (tangentAdditionRight addition-data)
  tangentAdditionDenominatorApart addition-data =
    tangentAdditionDenominatorApartFromCosineApart
      (fst (fst addition-data))
      (snd (fst addition-data))
      (snd addition-data)
