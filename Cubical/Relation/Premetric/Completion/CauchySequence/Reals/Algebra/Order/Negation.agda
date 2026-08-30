module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Negation where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals.Base

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.GroupLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Absorption
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Addition


neg-reverses≤ : ∀ x y →
  x ≤ℝ y → (Neg.- y) ≤ℝ (Neg.- x)
neg-reverses≤ x y x≤y =
    max-comm (Neg.- y) (Neg.- x)
  ∙ sym (neg-min x y)
  ∙ cong Neg.-_ (≤ℝ→min x y x≤y)

neg-reflects≤ : ∀ x y →
  (Neg.- y) ≤ℝ (Neg.- x) → x ≤ℝ y
neg-reflects≤ x y neg-y≤neg-x =
  subst2 _≤ℝ_
    (Neg.neg-involutive x) (Neg.neg-involutive y)
    (neg-reverses≤ (Neg.- y) (Neg.- x) neg-y≤neg-x)

≤→zero≤difference : ∀ x y →
  x ≤ℝ y → Real.ιℚ 0 ≤ℝ (y Group.- x)
≤→zero≤difference x y x≤y =
  subst (_≤ℝ (y Group.- x))
    (add-inverse-right x)
    (add-preserves≤-right x y (Neg.- x) x≤y)

zero≤difference→≤ : ∀ x y →
  Real.ιℚ 0 ≤ℝ (y Group.- x) → x ≤ℝ y
zero≤difference→≤ x y 0≤y-x =
  subst2 _≤ℝ_
    (add-zero-left x)
    (sub-add-cancel y x)
    (add-preserves≤-right (Real.ιℚ 0) (y Group.- x) x 0≤y-x)
