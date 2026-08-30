module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Order.Monotone.Strict where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Order.Monotone.Strict.Sealed


opaque
  expℝ-strictMono : ∀ {x y} →
    x <ℝ y → expℝ x <ℝ expℝ y
  expℝ-strictMono {x} {y} x<y =
    subst2 _<ℝ_
      (sealedExpℝ-agrees x)
      (sealedExpℝ-agrees y)
      (sealedExpℝ-strictMono x<y)
