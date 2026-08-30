module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Order.Monotone.NonStrict.Scaled where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Rationals.Base

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Negation
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Multiplication.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Bounds.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Order.Positive
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Order.Monotone.Difference
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Order.Monotone.GapBounds
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Order.Monotone.GapBounds.SealedOne
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Order.Monotone.GapBounds.SealedZero


scaled-expℝ-difference≤ : ∀ {x y} → x ≤ℝ y →
  sealedExpℝ x Mul.· Real.ιℚ 1 ≤ℝ
  sealedExpℝ x Mul.· sealedExpℝ (differenceℝ x y)
scaled-expℝ-difference≤ {x} {y} x≤y =
  mul-preserves≤-left-nonnegative-sealed
    (Real.ιℚ 1) (sealedExpℝ (differenceℝ x y)) (sealedExpℝ x)
    (one≤sealedExpℝ-difference x y x≤y)
    (zero≤sealedExpℝ x)
