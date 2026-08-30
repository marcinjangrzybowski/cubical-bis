module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Order.Monotone.GapBounds.SealedZero where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Rationals.Base

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Order.Monotone.GapBounds


opaque
  zero≤sealedExpℝ : ∀ x → Real.ιℚ 0 ≤ℝ sealedExpℝ x
  zero≤sealedExpℝ x =
    subst
      (Real.ιℚ 0 ≤ℝ_)
      (sym (sealedExpℝ-agrees x))
      (zero≤expℝ x)
