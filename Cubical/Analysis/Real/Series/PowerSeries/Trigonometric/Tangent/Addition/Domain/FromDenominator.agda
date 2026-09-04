module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Addition.Domain.FromDenominator where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Order.Apartness
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Addition.Domain.Base
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Addition.Factorization


-- A denominator gap is sufficient to construct the sum-domain point.

tangentAdditionFromDenominatorApartPair : (points : TangentPair) →
  0ℝ #ℝ
    tangentAdditionDenominator (fst points) (snd points) →
  TangentAdditionDomain
tangentAdditionFromDenominatorApartPair
    points denominator-apart =
  tangentAdditionDomainPoint points
    (tangentAdditionCosineApartFromDenominatorApart
      (fst points) (snd points) denominator-apart)


tangentAdditionFromDenominatorApart : ∀ left right →
  0ℝ #ℝ tangentAdditionDenominator left right →
  TangentAdditionDomain
tangentAdditionFromDenominatorApart
    left right denominator-apart =
  tangentAdditionFromDenominatorApartPair
    (left , right) denominator-apart
