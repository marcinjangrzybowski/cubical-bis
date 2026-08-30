module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Derivative.Sinh where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Derivative.Sealed.Sinh


opaque
  sinhℝHasDerivativeCoshℝ : IsDerivative sinhℝ coshℝ
  sinhℝHasDerivativeCoshℝ =
    subst2 IsDerivative
      sealedSinhℝ-agrees
      sealedCoshℝ-agrees
      sealedSinhℝHasDerivativeSealedCoshℝ
