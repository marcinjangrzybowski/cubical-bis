module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Multiplication.Sealed where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Rationals.Base

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Multiplication
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Multiplication


-- Stable boundaries for the completed-order multiplication proofs.  Their
-- transparent versions remain available to proofs that need computation.
opaque
  mul-preserves≤-left-nonnegative-sealed : ∀ x y z →
    x ≤ℝ y → Real.ιℚ 0 ≤ℝ z →
    (z Mul.· x) ≤ℝ (z Mul.· y)
  mul-preserves≤-left-nonnegative-sealed =
    mul-preserves≤-left-nonnegative


  mul-preserves≪-left-positive-sealed : ∀ x y z →
    x <ℝ y → Real.ιℚ 0 <ℝ z →
    (z Mul.· x) <ℝ (z Mul.· y)
  mul-preserves≪-left-positive-sealed =
    mul-preserves≪-left-positive
