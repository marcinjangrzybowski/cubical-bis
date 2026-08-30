module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Addition.Sealed where

open import Cubical.Foundations.Prelude

import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Addition


-- A normalization boundary for clients of the large Mertens construction.
-- The public law is unchanged; only its proof is sealed from downstream
-- equality checking.

opaque
  expℝ-add-sealed : ∀ x y →
    expℝ (x Add.+ y) ≡ expℝ x Mul.· expℝ y
  expℝ-add-sealed = expℝ-add
