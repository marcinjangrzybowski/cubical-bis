module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws.Sealed where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Rationals.Base

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.GroupLaws


-- A small opaque normalization boundary for clients that transport large
-- constructed functions along the additive inverse law.

opaque
  add-inverse-right-sealed : ∀ x →
    x Add.+ Neg.- x ≡ Real.ιℚ 0
  add-inverse-right-sealed = add-inverse-right


  neg-zero-sealed : Neg.- Real.ιℚ 0 ≡ Real.ιℚ 0
  neg-zero-sealed = neg-zero


  neg-add-sealed : ∀ x y →
    Neg.- (x Add.+ y) ≡ (Neg.- x) Add.+ (Neg.- y)
  neg-add-sealed = neg-add


  neg-involutive-sealed : ∀ x → Neg.- (Neg.- x) ≡ x
  neg-involutive-sealed = Neg.neg-involutive
