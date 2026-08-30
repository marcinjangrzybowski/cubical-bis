module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Rationals
open import Cubical.Data.Rationals.Base as ℚ

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Associativity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Associativity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Distributivity


ℝCommRing : CommRing ℓ-zero
ℝCommRing =
  makeCommRing
    (Real.ιℚ 0) (Real.ιℚ 1) Add._+_ Mul._·_ Neg.-_
    Real.Base.isSetCompletion
    add-assoc add-zero-right add-inverse-right add-comm
    mul-assoc mul-one-right mul-distrib-over-add-right mul-comm


ιℚIsCommRingHom :
  IsCommRingHom (snd ℚCommRing) Real.ιℚ (snd ℝCommRing)
ιℚIsCommRingHom =
  makeIsCommRingHom
    refl
    (λ p q → sym (Add.add-ι-ι p q))
    (λ p q → sym (Mul.mul-ι-ι p q))


ιℚCommRingHom : CommRingHom ℚCommRing ℝCommRing
ιℚCommRingHom = Real.ιℚ , ιℚIsCommRingHom
