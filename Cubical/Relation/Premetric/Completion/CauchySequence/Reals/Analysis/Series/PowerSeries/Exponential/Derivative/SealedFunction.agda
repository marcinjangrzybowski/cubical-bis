module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Derivative.SealedFunction where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Derivative.Sealed


opaque
  sealedExpℝ-function-agrees : sealedExpℝ ≡ expℝ
  sealedExpℝ-function-agrees = funExt sealedExpℝ-agrees


  sealedExpℝHasDerivativeSelf :
    IsDerivative sealedExpℝ sealedExpℝ
  sealedExpℝHasDerivativeSelf =
    subst2 IsDerivative
      (sym sealedExpℝ-function-agrees)
      (sym sealedExpℝ-function-agrees)
      expℝHasDerivativeSelf-sealed
