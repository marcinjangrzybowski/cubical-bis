module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Order.Monotone.NonStrict.Sealed where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Order.Monotone.Difference
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Order.Monotone.NonStrict.Scaled


opaque
  sealedExpℝ-mono : ∀ {x y} →
    x ≤ℝ y → sealedExpℝ x ≤ℝ sealedExpℝ y
  sealedExpℝ-mono {x} {y} x≤y =
    subst2 _≤ℝ_
      (mul-one-right (sealedExpℝ x))
      (sym (sealedExpℝ-difference-factorization x y))
      (scaled-expℝ-difference≤ x≤y)
