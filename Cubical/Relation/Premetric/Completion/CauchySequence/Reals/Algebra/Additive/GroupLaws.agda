module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.GroupLaws where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group.Properties
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Associativity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group

private
  module ℝGroup = GroupTheory (AbGroup→Group Group.ℝAbGroup)


neg-zero : Neg.- Real.ιℚ 0 ≡ Real.ιℚ 0
neg-zero = ℝGroup.inv1g

neg-add : ∀ x y →
  Neg.- (x Add.+ y) ≡ (Neg.- x) Add.+ (Neg.- y)
neg-add x y =
  ℝGroup.invDistr x y
  ∙ add-comm (Neg.- y) (Neg.- x)

sub-ι-ι : ∀ p q →
  Real.ιℚ p Group.- Real.ιℚ q ≡ Real.ιℚ (p ℚR.- q)
sub-ι-ι p q =
  cong (Real.ιℚ p Add.+_) (Neg.neg-ι q)
  ∙ Add.add-ι-ι p (ℚR.- q)
  ∙ cong Real.ιℚ ℚ!

sub-self : ∀ x → x Group.- x ≡ Real.ιℚ 0
sub-self = add-inverse-right

sub-zero-right : ∀ x → x Group.- Real.ιℚ 0 ≡ x
sub-zero-right x =
  cong (x Add.+_) neg-zero
  ∙ add-zero-right x

zero-sub : ∀ x → Real.ιℚ 0 Group.- x ≡ Neg.- x
zero-sub x = add-zero-left (Neg.- x)

neg-sub : ∀ x y →
  Neg.- (x Group.- y) ≡ y Group.- x
neg-sub x y =
  neg-add x (Neg.- y)
  ∙ cong ((Neg.- x) Add.+_) (Neg.neg-involutive y)
  ∙ add-comm (Neg.- x) y

sub-add-cancel : ∀ x y →
  (x Group.- y) Add.+ y ≡ x
sub-add-cancel x y =
  sym (add-assoc x (Neg.- y) y)
  ∙ cong (x Add.+_) (add-inverse-left y)
  ∙ add-zero-right x

add-sub-cancel : ∀ x y →
  (x Add.+ y) Group.- y ≡ x
add-sub-cancel x y =
  sym (add-assoc x y (Neg.- y))
  ∙ cong (x Add.+_) (add-inverse-right y)
  ∙ add-zero-right x

add-cancel-left : ∀ x {y z} →
  x Add.+ y ≡ x Add.+ z → y ≡ z
add-cancel-left = ℝGroup.·CancelL

add-cancel-right : ∀ {x y} z →
  x Add.+ z ≡ y Add.+ z → x ≡ y
add-cancel-right = ℝGroup.·CancelR
