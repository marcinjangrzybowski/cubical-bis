module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Scalar where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals
open import Cubical.Algebra.Module.Properties
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.NatPlusOne
open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Inverse
import Cubical.Data.Rationals.Order as ℚO
open import Cubical.Data.Rationals.Order.AbsoluteValue

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
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.GroupLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Scalar.Base
  as Scalar
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Scalar.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.RationalModule
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Addition
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.AbsoluteValue

open OrderedCommRingTheory ℚOrderedCommRing
open PositiveRationals
open 1/2∈ℚ


private
  module ℝModule = ModuleTheory
    (CommRing→Ring ℚCommRing) ℝLeftℚModule


scalar-neg : ∀ c x →
  c Scalar.⋆ (Neg.- x) ≡ Neg.- (c Scalar.⋆ x)
scalar-neg c x =
    cong (c Scalar.⋆_) (sym (ℝModule.minusByMult x))
  ∙ sym (scalar-assoc c (ℚR.- 1) x)
  ∙ cong (Scalar._⋆ x) ℚ!
  ∙ scalar-assoc (ℚR.- 1) c x
  ∙ ℝModule.minusByMult (c Scalar.⋆ x)

scalar-sub : ∀ c x y →
  c Scalar.⋆ (x Group.- y) ≡
  (c Scalar.⋆ x) Group.- (c Scalar.⋆ y)
scalar-sub c x y =
    scalar-dist-right c x (Neg.- y)
  ∙ cong ((c Scalar.⋆ x) Add.+_) (scalar-neg c y)

nonnegative-scalar-abs : ∀ c → 0 ℚO.≤ c → ∀ x →
  c Scalar.⋆ Abs.absℝ x ≡ Abs.absℝ (c Scalar.⋆ x)
nonnegative-scalar-abs c 0≤c x =
    cong (Scalar._⋆ Abs.absℝ x)
      (sym (0≤→abs≡id c 0≤c))
  ∙ sym (abs-scalar c x)


scalar-preserves-max : ∀ c → 0 ℚO.≤ c → ∀ x y →
  c Scalar.⋆ (x ⊔ℝ y) ≡
  (c Scalar.⋆ x) ⊔ℝ (c Scalar.⋆ y)
scalar-preserves-max c 0≤c x y =
    sym (scalar-assoc c rationalHalf body)
  ∙ cong (Scalar._⋆ body) ℚ!
  ∙ scalar-assoc rationalHalf c body
  ∙ cong (rationalHalf Scalar.⋆_)
      (scalar-dist-right c (x Add.+ y) (Abs.absℝ (x Group.- y))
      ∙ cong₂ Add._+_
          (scalar-dist-right c x y)
          (nonnegative-scalar-abs c 0≤c (x Group.- y)
          ∙ cong Abs.absℝ (scalar-sub c x y)))
  where
  body : Real.ℝ
  body = (x Add.+ y) Add.+ Abs.absℝ (x Group.- y)

scalar-preserves≤ : ∀ c → 0 ℚO.≤ c → ∀ x y →
  x ≤ℝ y → (c Scalar.⋆ x) ≤ℝ (c Scalar.⋆ y)
scalar-preserves≤ c 0≤c x y x≤y =
    sym (scalar-preserves-max c 0≤c x y)
  ∙ cong (c Scalar.⋆_) x≤y

positiveScalar-reflects≤ : ∀ c → ∀ x y →
  (fst c Scalar.⋆ x) ≤ℝ (fst c Scalar.⋆ y) → x ≤ℝ y
positiveScalar-reflects≤ c x y scaled =
  subst2 _≤ℝ_ (unscale x) (unscale y)
    (scalar-preserves≤ (fst (c ⁻¹₊))
      (ℚO.<Weaken≤ 0 (fst (c ⁻¹₊)) (snd (c ⁻¹₊)))
      (fst c Scalar.⋆ x) (fst c Scalar.⋆ y) scaled)
  where
  unscale : ∀ z →
    fst (c ⁻¹₊) Scalar.⋆ (fst c Scalar.⋆ z) ≡ z
  unscale z =
      sym (scalar-assoc (fst (c ⁻¹₊)) (fst c) z)
    ∙ cong (Scalar._⋆ z) (invℚ₊[x]·x c)
    ∙ scalar-id z


rationalHalfNonnegative : 0 ℚO.≤ rationalHalf
rationalHalfNonnegative =
  ℚO.<Weaken≤ 0 rationalHalf (snd [ 1 / 2 ]₊)

zero≤abs : ∀ x → Real.ιℚ 0 ≤ℝ Abs.absℝ x
zero≤abs x =
  subst2 _≤ℝ_ left-is-zero right-is-abs halves≤
  where
  halves≤ :
    (rationalHalf Scalar.⋆ x) Add.+
      (rationalHalf Scalar.⋆ (Neg.- x)) ≤ℝ
    (rationalHalf Scalar.⋆ Abs.absℝ x) Add.+
      (rationalHalf Scalar.⋆ Abs.absℝ x)
  halves≤ =
    add-monotone
      (rationalHalf Scalar.⋆ x)
      (rationalHalf Scalar.⋆ Abs.absℝ x)
      (rationalHalf Scalar.⋆ (Neg.- x))
      (rationalHalf Scalar.⋆ Abs.absℝ x)
      (scalar-preserves≤ rationalHalf rationalHalfNonnegative
        x (Abs.absℝ x) (x≤abs x))
      (scalar-preserves≤ rationalHalf rationalHalfNonnegative
        (Neg.- x) (Abs.absℝ x) (neg-x≤abs x))

  left-is-zero :
    (rationalHalf Scalar.⋆ x) Add.+
      (rationalHalf Scalar.⋆ (Neg.- x)) ≡ Real.ιℚ 0
  left-is-zero =
      sym (scalar-dist-right rationalHalf x (Neg.- x))
    ∙ cong (rationalHalf Scalar.⋆_) (add-inverse-right x)
    ∙ ℝModule.⋆AnnihilR rationalHalf

  right-is-abs :
    (rationalHalf Scalar.⋆ Abs.absℝ x) Add.+
      (rationalHalf Scalar.⋆ Abs.absℝ x) ≡ Abs.absℝ x
  right-is-abs =
      sym (scalar-dist-left rationalHalf rationalHalf (Abs.absℝ x))
    ∙ cong (Scalar._⋆ Abs.absℝ x) ℚ!
    ∙ scalar-id (Abs.absℝ x)
