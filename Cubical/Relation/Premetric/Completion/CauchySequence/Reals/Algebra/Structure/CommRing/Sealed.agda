module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing.Sealed where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing


-- An opaque presentation of the real commutative ring.  Generic algebra can
-- specialize to this record without unfolding the Cauchy-completion proofs;
-- clients can then transport the resulting proposition back to ℝCommRing.

opaque
  sealedℝCommRing : CommRing ℓ-zero
  sealedℝCommRing = ℝCommRing

  sealedℝCommRing-agrees : sealedℝCommRing ≡ ℝCommRing
  sealedℝCommRing-agrees = refl


  ℝCommRing-add-agrees :
    CommRingStr._+_ (snd ℝCommRing) ≡ Add._+_
  ℝCommRing-add-agrees = refl


  ℝCommRing-mul-agrees :
    CommRingStr._·_ (snd ℝCommRing) ≡ Mul._·_
  ℝCommRing-mul-agrees = refl


  ℝCommRing-neg-agrees :
    CommRingStr.-_ (snd ℝCommRing) ≡ Neg.-_
  ℝCommRing-neg-agrees = refl
