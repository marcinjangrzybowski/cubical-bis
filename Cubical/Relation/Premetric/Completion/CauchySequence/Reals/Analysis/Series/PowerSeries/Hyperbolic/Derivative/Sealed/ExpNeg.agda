module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Derivative.Sealed.ExpNeg where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Chain
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Derivative.SealedFunction
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Coefficients
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Shapes
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Derivative.NegativeIdentity


opaque
  sealedExpℝNegHasDerivativeNegativeSelf :
    IsDerivative
      (sealedExpℝ ∘ Neg.-_)
      (Neg.-_ ∘ sealedExpℝ ∘ Neg.-_)
  sealedExpℝNegHasDerivativeNegativeSelf =
    subst
      (IsDerivative (sealedExpℝ ∘ Neg.-_))
      derivative-path
      (chainHasDerivative
        Neg.-_ (λ _ → Neg.- oneℝ)
        sealedExpℝ sealedExpℝ
        negativeIdentityHasDerivativeNegativeOne
        sealedExpℝHasDerivativeSelf)
    where
    derivative-path :
      (λ x → sealedExpℝ (Neg.- x) Mul.· (Neg.- oneℝ))
        ≡ (Neg.-_ ∘ sealedExpℝ ∘ Neg.-_)
    derivative-path =
      funExt λ x →
        HyperbolicAlgebra.exp-neg-derivative-shape ℝCommRing
          (sealedExpℝ (Neg.- x))
