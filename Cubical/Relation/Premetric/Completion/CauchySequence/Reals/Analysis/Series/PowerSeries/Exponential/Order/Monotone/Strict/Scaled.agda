module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Order.Monotone.Strict.Scaled where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Rationals.Base

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Multiplication.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Order.Monotone.Difference
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Order.Monotone.Strict.GapBound.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Order.Monotone.Strict.Positive.Sealed


opaque
  scaled-sealedExpℝ-difference< : ∀ {x y} → x <ℝ y →
    sealedExpℝ x Mul.· Real.ιℚ 1 <ℝ
    sealedExpℝ x Mul.· sealedExpℝ (differenceℝ x y)
  scaled-sealedExpℝ-difference< {x} {y} x<y =
    mul-preserves≪-left-positive-sealed
      (Real.ιℚ 1) (sealedExpℝ (differenceℝ x y)) (sealedExpℝ x)
      (one<sealedExpℝ-difference x y x<y)
      (zero<sealedExpℝ x)
