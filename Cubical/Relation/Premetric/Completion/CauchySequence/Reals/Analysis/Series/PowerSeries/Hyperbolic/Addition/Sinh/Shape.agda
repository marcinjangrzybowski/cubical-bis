module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Addition.Sinh.Shape where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Addition.Sinh.Terms
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Addition.Sinh.Shape.Polynomial


opaque
  sinhℝ-add-shape : ∀ x y →
    sinhAddScaled x y ≡ sinhAddShaped x y
  sinhℝ-add-shape = sinhℝ-add-polynomial
