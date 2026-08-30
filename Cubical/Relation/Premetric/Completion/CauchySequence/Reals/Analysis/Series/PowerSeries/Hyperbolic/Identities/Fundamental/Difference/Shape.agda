module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.Fundamental.Difference.Shape where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.Shapes.Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.Fundamental.Difference.Terms

opaque
  fundamentalParity≡difference : ∀ x →
    fundamentalParity x ≡ fundamentalDifference x
  fundamentalParity≡difference x =
    negative-product-real (coshℝ x) (sinhℝ x)
