module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Bounds.Sealed where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals.Base

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential


-- Downstream order algebra only needs these completed bounds as facts.  The
-- analytic partial-sum proofs remain available from `Exponential`, while
-- these opaque forms avoid re-normalizing those proofs at every use site.
opaque
  one≤expℝOfNonnegative-sealed : ∀ x →
    zeroℝ ≤ℝ x → Real.ιℚ 1 ≤ℝ expℝ x
  one≤expℝOfNonnegative-sealed = one≤expℝOfNonnegative


  expℝPositiveOfNonnegative-sealed : ∀ x →
    zeroℝ ≤ℝ x → zeroℝ <ℝ expℝ x
  expℝPositiveOfNonnegative-sealed = expℝPositiveOfNonnegative
