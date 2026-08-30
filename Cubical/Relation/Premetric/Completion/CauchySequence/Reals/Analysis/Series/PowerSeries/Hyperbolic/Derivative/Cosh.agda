module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Derivative.Cosh where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Derivative.Sealed.Cosh


opaque
  coshℝHasDerivativeSinhℝ : IsDerivative coshℝ sinhℝ
  coshℝHasDerivativeSinhℝ =
    subst2 IsDerivative
      sealedCoshℝ-agrees
      sealedSinhℝ-agrees
      sealedCoshℝHasDerivativeSealedSinhℝ
