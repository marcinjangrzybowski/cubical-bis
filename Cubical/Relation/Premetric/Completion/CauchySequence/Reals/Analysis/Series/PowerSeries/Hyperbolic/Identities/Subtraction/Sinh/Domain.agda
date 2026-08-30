module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.Subtraction.Sinh.Domain where

open import Cubical.Foundations.Prelude
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation as Neg
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup as Group
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Congruence.Sealed

opaque
  sinh-sub-domain : ∀ x y →
    sinhℝ (x Group.- y) ≡ sinhℝ (x Add.+ (Neg.- y))
  sinh-sub-domain x y = sinhℝ-cong-sealed (sub-definition-sealed x y)
