module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Laws.Negation where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Rationals.Base

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Laws.Zero
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Laws.Negation.AddInverse
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Laws.Negation.Addition


-- Keep the completed multiplicative laws opaque.  Clients need their
-- statements, but normalizing through the addition theorem and the power
-- series construction makes otherwise small reciprocal arguments expensive.
opaque
  expℝ-mul-neg : ∀ x →
    expℝ x Mul.· expℝ (Neg.- x) ≡ Real.ιℚ 1
  expℝ-mul-neg x =
      expℝ-product-as-add-inverse x
    ∙ expℝ-add-inverse x
    ∙ expℝ-zero


  expℝ-neg-mul : ∀ x →
    expℝ (Neg.- x) Mul.· expℝ x ≡ Real.ιℚ 1
  expℝ-neg-mul x =
    mul-comm (expℝ (Neg.- x)) (expℝ x)
    ∙ expℝ-mul-neg x
