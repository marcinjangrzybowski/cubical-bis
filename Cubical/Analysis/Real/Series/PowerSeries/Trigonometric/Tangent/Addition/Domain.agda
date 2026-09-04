module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Addition.Domain where

open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Addition.Domain.Base public
  using
    ( TangentPair
    ; tangentPairSum
    ; TangentAdditionDomain
    ; tangentAdditionLeft
    ; tangentAdditionRight
    ; tangentAdditionSumPoint
    ; tangentAdditionDenominator
    ; tangentAdditionNumerator
    ; secantAdditionNumerator
    ; tangentAdditionCommonCosineFactor
    )
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Addition.Factorization public
  using
    ( tangentAdditionCosineFactorization
    ; tangentAdditionSineFactorization
    ; tangentAdditionCommonFactorApart
    )
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Addition.Domain.FromDenominator public
  using (tangentAdditionFromDenominatorApart)
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Addition.Domain.DenominatorApart public
  using (tangentAdditionDenominatorApart)
