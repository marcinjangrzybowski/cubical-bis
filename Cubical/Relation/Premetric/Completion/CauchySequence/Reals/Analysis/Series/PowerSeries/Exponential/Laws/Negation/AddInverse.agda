module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Laws.Negation.AddInverse where

open import Cubical.Foundations.Prelude

import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Sealed


opaque
  expℝ-add-inverse : ∀ x →
    expℝ (x Add.+ Neg.- x) ≡ expℝ zeroℝ
  expℝ-add-inverse x =
      sym (sealedExpℝ-agrees (x Add.+ Neg.- x))
    ∙ sealedExpℝ-cong (add-inverse-right-sealed x)
    ∙ sealedExpℝ-agrees zeroℝ
