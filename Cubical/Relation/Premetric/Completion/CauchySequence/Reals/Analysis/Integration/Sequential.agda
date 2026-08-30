module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.Sequential where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Sequence
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Integration.Partition


quadratureSequence : ∀ {a b} →
  (ℕ → TaggedPartition[ a , b ]) →
  (Real.ℝ → Real.ℝ) → ℕ → Real.ℝ
quadratureSequence partitions f n =
  riemannSum (partitions n) f


-- A Cauchy quadrature separates the analytic and completion layers.  The
-- analytic front-end supplies a canonical partition family and proves its
-- sums Cauchy.  The completion consumes the radiuswise Cauchy proof directly,
-- so integration never assembles a global modulus of convergence.

record CauchyQuadrature
  (a b : Real.ℝ) (f : Real.ℝ → Real.ℝ) : Type₀ where
  field
    partitions : ℕ → TaggedPartition[ a , b ]
    sumsCauchy : IsCauchySequence (quadratureSequence partitions f)


quadratureValue : ∀ {a b f} →
  CauchyQuadrature a b f → Real.ℝ
quadratureValue {f = f} q =
  limitOfCauchySequence
    (quadratureSequence
      (CauchyQuadrature.partitions q) f)
    (CauchyQuadrature.sumsCauchy q)


quadratureValueIsLimit : ∀ {a b f}
  (q : CauchyQuadrature a b f) →
  isLimitSequence
    (quadratureSequence (CauchyQuadrature.partitions q) f)
    (quadratureValue q)
quadratureValueIsLimit {f = f} q =
  limitOfCauchySequenceIsLimit
    (quadratureSequence (CauchyQuadrature.partitions q) f)
    (CauchyQuadrature.sumsCauchy q)


-- Scheme independence asks for asymptotic closeness one radius at a time.
-- This is the right interface for comparing left, right, midpoint, or refined
-- quadratures without choosing all comparison cutoffs simultaneously.

equivalentQuadraturesHaveEqualValue : ∀ {a b f}
  (q r : CauchyQuadrature a b f) →
  EventuallyClose
    (quadratureSequence (CauchyQuadrature.partitions q) f)
    (quadratureSequence (CauchyQuadrature.partitions r) f) →
  quadratureValue q ≡ quadratureValue r
equivalentQuadraturesHaveEqualValue {f = f} q r close =
  sym (canonicalLimit≡
    (quadratureSequence (CauchyQuadrature.partitions r) f)
    (CauchyQuadrature.sumsCauchy r)
    (quadratureValue q)
    (eventuallyClosePresIsLimitSequence close
      (quadratureValueIsLimit q)))
