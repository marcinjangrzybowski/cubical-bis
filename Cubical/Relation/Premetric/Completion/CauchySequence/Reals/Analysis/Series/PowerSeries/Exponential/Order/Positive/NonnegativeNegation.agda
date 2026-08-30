module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Order.Positive.NonnegativeNegation where

open import Cubical.Foundations.Prelude

import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Associativity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Inverse.Positive
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Inverse.Order
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Laws


-- On the nonnegative half-line the addition law already identifies exp(-x)
-- with the constructed positive reciprocal of exp(x).  This intermediate
-- form is useful because it does not require global positivity as an input.

expℝ-neg-as-positiveReciprocal-of-nonnegative : ∀ x →
  (0≤x : zeroℝ ≤ℝ x) →
  expℝ (Neg.- x) ≡
    positiveReciprocal (expℝ x)
      (expℝPositiveOfNonnegative x 0≤x)
expℝ-neg-as-positiveReciprocal-of-nonnegative x 0≤x =
    sym (mul-one-left (expℝ (Neg.- x)))
  ∙ cong
      (Mul._· expℝ (Neg.- x))
      (sym (positiveReciprocalLaw'
        (expℝ x) (expℝPositiveOfNonnegative x 0≤x)))
  ∙ sym
      (mul-assoc
        (positiveReciprocal (expℝ x)
          (expℝPositiveOfNonnegative x 0≤x))
        (expℝ x) (expℝ (Neg.- x)))
  ∙ cong
      (positiveReciprocal (expℝ x)
        (expℝPositiveOfNonnegative x 0≤x) Mul.·_)
      (expℝ-mul-neg x)
  ∙ mul-one-right
      (positiveReciprocal (expℝ x)
        (expℝPositiveOfNonnegative x 0≤x))


expℝ-neg-positiveOfNonnegative : ∀ x →
  zeroℝ ≤ℝ x → zeroℝ <ℝ expℝ (Neg.- x)
expℝ-neg-positiveOfNonnegative x 0≤x =
  subst (zeroℝ <ℝ_)
    (sym (expℝ-neg-as-positiveReciprocal-of-nonnegative x 0≤x))
    (positiveReciprocalPositive
      (expℝ x) (expℝPositiveOfNonnegative x 0≤x))
