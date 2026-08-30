module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.AbGroup
open import Cubical.Data.Rationals.Base as ℚ

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Associativity


infixl 6 _-_

_-_ : Real.ℝ → Real.ℝ → Real.ℝ
x - y = x Add.+ (Neg.- y)


-- Thus the additive structure does not depend on a comparison equivalence
-- with either existing real construction.

ℝAbGroup : AbGroup ℓ-zero
ℝAbGroup =
  makeAbGroup (Real.ιℚ 0) Add._+_ Neg.-_
    Real.Base.isSetCompletion add-assoc add-zero-right
    add-inverse-right add-comm
