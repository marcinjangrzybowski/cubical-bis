module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Derivative.Sealed where

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential


opaque
  expℝHasDerivativeSelf-sealed : IsDerivative expℝ expℝ
  expℝHasDerivativeSelf-sealed = expℝHasDerivativeSelf
