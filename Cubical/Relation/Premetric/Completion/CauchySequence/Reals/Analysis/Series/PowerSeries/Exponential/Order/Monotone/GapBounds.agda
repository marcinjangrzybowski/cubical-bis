module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Order.Monotone.GapBounds where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Rationals.Base

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Bounds.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Order.Positive
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Order.Monotone.Difference


opaque
  one≤expℝ-difference : ∀ x y → x ≤ℝ y →
    Real.ιℚ 1 ≤ℝ expℝ (differenceℝ x y)
  one≤expℝ-difference x y x≤y =
    one≤expℝOfNonnegative-sealed (differenceℝ x y)
      (≤→zero≤difference-sealed x y x≤y)


  zero≤expℝ : ∀ x → Real.ιℚ 0 ≤ℝ expℝ x
  zero≤expℝ x =
    <ℝ-weaken-sealed zeroℝ (expℝ x) (expℝ-positive x)
