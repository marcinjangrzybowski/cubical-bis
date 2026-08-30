module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Order.Monotone.Strict.GapBound.Sealed where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Rationals.Base

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Order.Monotone.Difference
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Order.Monotone.Strict.GapBound


opaque
  one<sealedExpℝ-difference : ∀ x y → x <ℝ y →
    Real.ιℚ 1 <ℝ sealedExpℝ (differenceℝ x y)
  one<sealedExpℝ-difference x y x<y =
    subst
      (Real.ιℚ 1 <ℝ_)
      (sym (sealedExpℝ-agrees (differenceℝ x y)))
      (one<expℝ-difference x y x<y)
