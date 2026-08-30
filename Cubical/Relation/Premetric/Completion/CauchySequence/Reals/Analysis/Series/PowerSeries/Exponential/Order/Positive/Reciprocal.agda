module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Order.Positive.Reciprocal where

open import Cubical.Foundations.Prelude

import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Associativity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Inverse.Positive
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Inverse.Positive.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Inverse.Signed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Order.Positive.Global


-- Once positivity is global, negation is globally represented by the
-- positive reciprocal, and subtraction becomes multiplication by that
-- reciprocal.  These laws expose a division-free API suitable for later
-- logarithm work.

opaque
  expℝ-neg-as-positiveReciprocal : ∀ x →
    expℝ (Neg.- x) ≡
      positiveReciprocal (expℝ x) (expℝ-positive x)
  expℝ-neg-as-positiveReciprocal x =
    mul-cancel-left-apart
      (expℝ (Neg.- x))
      (positiveReciprocal (expℝ x) (expℝ-positive x))
      (expℝ x)
      (expℝ-apart-zero x)
      ( expℝ-mul-neg x
      ∙ sym (positiveReciprocalLaw-sealed
          (expℝ x) (expℝ-positive x)))
