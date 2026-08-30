module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.Fundamental.Difference.AtZero.Inverse where

open import Cubical.Foundations.Prelude
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation as Neg
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Constants.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Congruence.Sealed

opaque
  cosh-zero≡cosh-add-inverse : ∀ x →
    coshℝ zeroℝ ≡ coshℝ (x Add.+ (Neg.- x))
  cosh-zero≡cosh-add-inverse x =
    coshℝ-cong-sealed
      (sym rationalZero≡zeroℝ ∙ sym (add-inverse-right-sealed x))
