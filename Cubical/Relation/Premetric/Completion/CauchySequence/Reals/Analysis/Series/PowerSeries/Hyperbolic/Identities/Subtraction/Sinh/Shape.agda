module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.Subtraction.Sinh.Shape where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.Shapes.Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.Subtraction.Terms

opaque
  sinh-sub-shape : ∀ x y →
    sinhSubParity (sinhℝ x) (sinhℝ y) (coshℝ x) (coshℝ y) ≡
      sinhSubResult (sinhℝ x) (sinhℝ y) (coshℝ x) (coshℝ y)
  sinh-sub-shape x y =
    sinh-sub-shape-real
      (sinhℝ x) (sinhℝ y) (coshℝ x) (coshℝ y)
