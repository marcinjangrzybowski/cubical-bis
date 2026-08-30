module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Derivative.Sealed.Sinh.Difference where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Algebra.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Derivative.SealedFunction
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Derivative.Sealed.ExpNeg


opaque
  sealedExpℝDifferenceHasDerivative :
    IsDerivative
      (λ x → sealedExpℝ x Group.- (sealedExpℝ ∘ Neg.-_) x)
      (λ x → sealedExpℝ x Group.-
        (Neg.-_ ∘ sealedExpℝ ∘ Neg.-_) x)
  sealedExpℝDifferenceHasDerivative =
    subHasDerivative-sealed
      sealedExpℝ (sealedExpℝ ∘ Neg.-_)
      sealedExpℝ (Neg.-_ ∘ sealedExpℝ ∘ Neg.-_)
      sealedExpℝHasDerivativeSelf
      sealedExpℝNegHasDerivativeNegativeSelf
