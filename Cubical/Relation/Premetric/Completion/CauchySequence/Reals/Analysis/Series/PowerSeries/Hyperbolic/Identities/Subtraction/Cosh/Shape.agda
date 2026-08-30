module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.Subtraction.Cosh.Shape where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.Shapes.Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.Subtraction.Terms

opaque
  cosh-sub-shape : ∀ x y →
    coshSubParity (coshℝ x) (coshℝ y) (sinhℝ x) (sinhℝ y) ≡
      coshSubResult (coshℝ x) (coshℝ y) (sinhℝ x) (sinhℝ y)
  cosh-sub-shape x y =
    cosh-sub-shape-real
      (sinhℝ x) (sinhℝ y) (coshℝ x) (coshℝ y)
