module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Derivative.ExpNeg where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Chain
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Coefficients
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Shapes
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Derivative.NegativeIdentity


opaque
  expℝNegHasDerivativeNegativeSelf :
    IsDerivative
      (expℝ ∘ Neg.-_)
      (Neg.-_ ∘ expℝ ∘ Neg.-_)
  expℝNegHasDerivativeNegativeSelf =
    subst
      (IsDerivative (expℝ ∘ Neg.-_))
      derivative-path
      (chainHasDerivative
        Neg.-_ (λ _ → Neg.- oneℝ)
        expℝ expℝ
        negativeIdentityHasDerivativeNegativeOne
        expℝHasDerivativeSelf)
    where
    derivative-path :
      (λ x → expℝ (Neg.- x) Mul.· (Neg.- oneℝ))
        ≡ (Neg.-_ ∘ expℝ ∘ Neg.-_)
    derivative-path =
      funExt λ x →
        HyperbolicAlgebra.exp-neg-derivative-shape ℝCommRing
          (expℝ (Neg.- x))
