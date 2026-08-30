module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Inverse.Positive.Sealed where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Rationals.Base

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Inverse.Positive


-- A conversion boundary for clients that only need the reciprocal law, not
-- normalization through its Cauchy-completion construction.
opaque
  positiveReciprocalLaw-sealed : ∀ x
    (p : Real.ιℚ 0 <ℝ x) →
    x Mul.· positiveReciprocal x p ≡ Real.ιℚ 1
  positiveReciprocalLaw-sealed = positiveReciprocalLaw
