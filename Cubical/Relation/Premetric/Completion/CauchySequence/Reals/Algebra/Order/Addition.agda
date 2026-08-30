module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Addition where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.AbGroup
open import Cubical.Data.Rationals.Base as ℚ

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Associativity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.GroupLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Scalar.Base
  as Scalar
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Scalar.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base


private
  maxBody : Real.ℝ → Real.ℝ → Real.ℝ
  maxBody x y =
    (x Add.+ y) Add.+ Abs.absℝ (x Group.- y)

  translated-sum : ∀ x y z →
    (x Add.+ z) Add.+ (y Add.+ z) ≡
    (x Add.+ y) Add.+ (z Add.+ z)
  translated-sum x y z =
      sym (add-assoc x z (y Add.+ z))
    ∙ cong (x Add.+_)
        (add-assoc z y z
        ∙ cong (Add._+ z) (add-comm z y)
        ∙ sym (add-assoc y z z))
    ∙ add-assoc x y (z Add.+ z)

  translated-difference : ∀ x y z →
    (x Add.+ z) Group.- (y Add.+ z) ≡ x Group.- y
  translated-difference x y z =
      cong ((x Add.+ z) Add.+_) (neg-add y z)
    ∙ rearrange x y z
    ∙ cong ((x Group.- y) Add.+_) (add-inverse-right z)
    ∙ add-zero-right (x Group.- y)
    where
    rearrange : ∀ x y z →
      (x Add.+ z) Add.+ ((Neg.- y) Add.+ (Neg.- z)) ≡
      (x Add.+ (Neg.- y)) Add.+ (z Add.+ (Neg.- z))
    rearrange x y z =
        sym (add-assoc x z ((Neg.- y) Add.+ (Neg.- z)))
      ∙ cong (x Add.+_)
          (add-assoc z (Neg.- y) (Neg.- z)
          ∙ cong (Add._+ (Neg.- z)) (add-comm z (Neg.- y))
          ∙ sym (add-assoc (Neg.- y) z (Neg.- z)))
      ∙ add-assoc x (Neg.- y) (z Add.+ (Neg.- z))

  maxBody-translate : ∀ x y z →
    maxBody (x Add.+ z) (y Add.+ z) ≡
    maxBody x y Add.+ (z Add.+ z)
  maxBody-translate x y z =
      cong₂ Add._+_
        (translated-sum x y z)
        (cong Abs.absℝ (translated-difference x y z))
    ∙ reassociate (x Add.+ y) (Abs.absℝ (x Group.- y)) z
    where
    reassociate : ∀ a b z →
      (a Add.+ (z Add.+ z)) Add.+ b ≡
      (a Add.+ b) Add.+ (z Add.+ z)
    reassociate a b z =
        sym (add-assoc a (z Add.+ z) b)
      ∙ cong (a Add.+_) (add-comm (z Add.+ z) b)
      ∙ add-assoc a b (z Add.+ z)

  half-double : ∀ z →
    rationalHalf Scalar.⋆ (z Add.+ z) ≡ z
  half-double z =
      scalar-dist-right rationalHalf z z
    ∙ sym (scalar-dist-left rationalHalf rationalHalf z)
    ∙ cong (Scalar._⋆ z) ℚ!
    ∙ scalar-id z


max-translate-right : ∀ x y z →
  (x ⊔ℝ y) Add.+ z ≡
  (x Add.+ z) ⊔ℝ (y Add.+ z)
max-translate-right x y z =
  sym
    (cong (rationalHalf Scalar.⋆_) (maxBody-translate x y z)
    ∙ scalar-dist-right rationalHalf (maxBody x y) (z Add.+ z)
    ∙ cong ((rationalHalf Scalar.⋆ maxBody x y) Add.+_) (half-double z))

max-translate-left : ∀ z x y →
  z Add.+ (x ⊔ℝ y) ≡
  (z Add.+ x) ⊔ℝ (z Add.+ y)
max-translate-left z x y =
    add-comm z (x ⊔ℝ y)
  ∙ max-translate-right x y z
  ∙ cong₂ _⊔ℝ_ (add-comm x z) (add-comm y z)


add-preserves≤-right : ∀ x y z →
  x ≤ℝ y → (x Add.+ z) ≤ℝ (y Add.+ z)
add-preserves≤-right x y z x≤y =
    sym (max-translate-right x y z)
  ∙ cong (Add._+ z) x≤y

add-preserves≤-left : ∀ x y z →
  x ≤ℝ y → (z Add.+ x) ≤ℝ (z Add.+ y)
add-preserves≤-left x y z x≤y =
    sym (max-translate-left z x y)
  ∙ cong (z Add.+_) x≤y

add-reflects≤-right : ∀ x y z →
  (x Add.+ z) ≤ℝ (y Add.+ z) → x ≤ℝ y
add-reflects≤-right x y z translated =
  subst2 _≤ℝ_
    (add-sub-cancel x z) (add-sub-cancel y z)
    (add-preserves≤-right
      (x Add.+ z) (y Add.+ z) (Neg.- z) translated)

add-reflects≤-left : ∀ x y z →
  (z Add.+ x) ≤ℝ (z Add.+ y) → x ≤ℝ y
add-reflects≤-left x y z translated =
  add-reflects≤-right x y z
    (subst2 _≤ℝ_
      (add-comm z x) (add-comm z y) translated)
