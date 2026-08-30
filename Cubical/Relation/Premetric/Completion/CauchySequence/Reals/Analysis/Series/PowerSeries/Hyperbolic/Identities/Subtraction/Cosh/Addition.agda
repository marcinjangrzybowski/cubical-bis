module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.Subtraction.Cosh.Addition where

open import Cubical.Foundations.Prelude
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation as Neg
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition as Add
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.Subtraction.Terms

opaque
  cosh-sub-addition : ∀ x y →
    coshℝ (x Add.+ (Neg.- y)) ≡ coshSubAdded (coshℝ x) (sinhℝ x) y
  cosh-sub-addition x y = coshℝ-add x (Neg.- y)
