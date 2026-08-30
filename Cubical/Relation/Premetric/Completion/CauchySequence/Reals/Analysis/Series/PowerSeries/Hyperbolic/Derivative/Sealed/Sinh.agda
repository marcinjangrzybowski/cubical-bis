module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Derivative.Sealed.Sinh where

open import Cubical.Foundations.Prelude

import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Algebra.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Coefficients
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Sealed.Definitions
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Derivative.Sealed.Sinh.Difference
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Derivative.Sealed.Sinh.OutputAgreement


opaque
  sealedSinhℝHasDerivativeSealedCoshℝ :
    IsDerivative sealedSinhℝ sealedCoshℝ
  sealedSinhℝHasDerivativeSealedCoshℝ =
    subst (IsDerivative sealedSinhℝ)
      sealedSinhDerivative-agrees
      (scaleHasDerivative-sealed
        (λ x → sealedExpℝ x Group.- sealedExpℝ (Neg.- x))
        (λ x → sealedExpℝ x Group.-
          (Neg.- sealedExpℝ (Neg.- x)))
        halfℝ
        sealedExpℝDifferenceHasDerivative)
