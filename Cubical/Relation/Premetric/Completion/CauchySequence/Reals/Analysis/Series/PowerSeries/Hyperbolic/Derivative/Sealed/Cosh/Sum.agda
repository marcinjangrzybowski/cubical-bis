module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Derivative.Sealed.Cosh.Sum where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Algebra.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Derivative.SealedFunction
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Derivative.Sealed.ExpNeg


opaque
  sealedExpℝSumHasDerivative :
    IsDerivative
      (λ x → sealedExpℝ x Add.+ (sealedExpℝ ∘ Neg.-_) x)
      (λ x → sealedExpℝ x Add.+
        (Neg.-_ ∘ sealedExpℝ ∘ Neg.-_) x)
  sealedExpℝSumHasDerivative =
    addHasDerivative-sealed
      sealedExpℝ (sealedExpℝ ∘ Neg.-_)
      sealedExpℝ (Neg.-_ ∘ sealedExpℝ ∘ Neg.-_)
      sealedExpℝHasDerivativeSelf
      sealedExpℝNegHasDerivativeNegativeSelf
