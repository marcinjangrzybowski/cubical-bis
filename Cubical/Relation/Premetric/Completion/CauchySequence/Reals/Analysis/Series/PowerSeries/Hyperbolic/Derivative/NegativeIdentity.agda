module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Derivative.NegativeIdentity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Algebra
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Basic
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Coefficients


opaque
  negativeIdentityHasDerivativeNegativeOne :
    IsDerivative Neg.-_ (λ _ → Neg.- oneℝ)
  negativeIdentityHasDerivativeNegativeOne =
    negHasDerivative
      (idfun Real.ℝ) (λ _ → oneℝ)
      identityHasDerivative
