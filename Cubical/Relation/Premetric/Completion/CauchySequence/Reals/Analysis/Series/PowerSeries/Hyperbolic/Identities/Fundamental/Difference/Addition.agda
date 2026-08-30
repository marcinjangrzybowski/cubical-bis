module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.Fundamental.Difference.Addition where

open import Cubical.Foundations.Prelude
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation as Neg
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.Fundamental.Difference.Terms

opaque
  cosh-add-inverse≡translated : ∀ x →
    coshℝ (x Add.+ (Neg.- x)) ≡ fundamentalTranslated x
  cosh-add-inverse≡translated x = coshℝ-add x (Neg.- x)
