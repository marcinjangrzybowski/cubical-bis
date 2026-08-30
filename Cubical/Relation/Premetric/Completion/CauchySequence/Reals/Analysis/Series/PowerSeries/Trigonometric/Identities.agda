module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Trigonometric.Identities where

open import Cubical.Foundations.Prelude
open import Cubical.Tactics.CommRingSolver

open import Cubical.Algebra.CommRing
open import Cubical.Data.Rationals.Base
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.GroupLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Trigonometric
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Trigonometric.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Trigonometric.Addition


private
  module IdentityAlgebra {ℓ} (R : CommRing ℓ) where
    open CommRingStr (snd R)
    open import Cubical.Algebra.Ring.Properties
    open RingTheory (CommRing→Ring R)

    negative-product : ∀ cosine sine →
      cosine · cosine - sine · (- sine)
        ≡ cosine · cosine + sine · sine
    negative-product cosine sine = solve! R

    cosine-as-total-minus-double-sine : ∀ cosine sine →
      cosine · cosine - sine · sine
        ≡
      (cosine · cosine + sine · sine) -
        (sine · sine + sine · sine)
    cosine-as-total-minus-double-sine cosine sine = solve! R

    cosine-as-double-cosine-minus-total : ∀ cosine sine →
      cosine · cosine - sine · sine
        ≡
      (cosine · cosine + cosine · cosine) -
        (cosine · cosine + sine · sine)
    cosine-as-double-cosine-minus-total cosine sine = solve! R


-- Pythagorean identity -------------------------------------------------
--
-- Evaluating cos(x + -x) by the addition formula yields the sum of the
-- two squares.  Its left side is cos(0), hence one.  No analytic argument
-- beyond the already checked total addition and parity laws is needed.

one≡cosSquare-add-sinSquare : ∀ x →
  Real.ιℚ 1 ≡
    (cosℝ x Mul.· cosℝ x) Add.+
      (sinℝ x Mul.· sinℝ x)
one≡cosSquare-add-sinSquare x =
    sym cosℝ-zero
  ∙ cong cosℝ (sym (add-inverse-right x))
  ∙ cosℝ-add x (Neg.- x)
  ∙ cong₂ Group._-_
      (cong (cosℝ x Mul.·_) (cosℝ-neg x))
      (cong (sinℝ x Mul.·_) (sinℝ-neg x))
  ∙ IdentityAlgebra.negative-product ℝCommRing
      (cosℝ x) (sinℝ x)


cosSquare-add-sinSquare≡one : ∀ x →
  (cosℝ x Mul.· cosℝ x) Add.+
      (sinℝ x Mul.· sinℝ x)
    ≡ Real.ιℚ 1
cosSquare-add-sinSquare≡one x =
  sym (one≡cosSquare-add-sinSquare x)


sinSquare-add-cosSquare≡one : ∀ x →
  (sinℝ x Mul.· sinℝ x) Add.+
      (cosℝ x Mul.· cosℝ x)
    ≡ Real.ιℚ 1
sinSquare-add-cosSquare≡one x =
    add-comm
      (sinℝ x Mul.· sinℝ x)
      (cosℝ x Mul.· cosℝ x)
  ∙ cosSquare-add-sinSquare≡one x


sinSquare≡one-sub-cosSquare : ∀ x →
  sinℝ x Mul.· sinℝ x
    ≡ Real.ιℚ 1 Group.- (cosℝ x Mul.· cosℝ x)
sinSquare≡one-sub-cosSquare x =
    sym
      (add-sub-cancel
        (sinℝ x Mul.· sinℝ x)
        (cosℝ x Mul.· cosℝ x))
  ∙ cong
      (Group._- (cosℝ x Mul.· cosℝ x))
      (sinSquare-add-cosSquare≡one x)


cosSquare≡one-sub-sinSquare : ∀ x →
  cosℝ x Mul.· cosℝ x
    ≡ Real.ιℚ 1 Group.- (sinℝ x Mul.· sinℝ x)
cosSquare≡one-sub-sinSquare x =
    sym
      (add-sub-cancel
        (cosℝ x Mul.· cosℝ x)
        (sinℝ x Mul.· sinℝ x))
  ∙ cong
      (Group._- (sinℝ x Mul.· sinℝ x))
      (cosSquare-add-sinSquare≡one x)


-- Double-angle identities ---------------------------------------------

sinℝ-double : ∀ x →
  sinℝ (x Add.+ x)
    ≡ (sinℝ x Mul.· cosℝ x) Add.+
        (sinℝ x Mul.· cosℝ x)
sinℝ-double x =
    sinℝ-add x x
  ∙ cong ((sinℝ x Mul.· cosℝ x) Add.+_)
      (mul-comm (cosℝ x) (sinℝ x))


cosℝ-double : ∀ x →
  cosℝ (x Add.+ x)
    ≡ (cosℝ x Mul.· cosℝ x) Group.-
        (sinℝ x Mul.· sinℝ x)
cosℝ-double x = cosℝ-add x x


-- Combining the direct cosine double-angle formula with Pythagoras gives
-- the two standard squared forms without introducing a separate numeral-2
-- scalar API: doubling is represented by native addition.

cosℝ-double≡one-sub-doubleSinSquare : ∀ x →
  cosℝ (x Add.+ x)
    ≡ Real.ιℚ 1 Group.-
      ((sinℝ x Mul.· sinℝ x) Add.+
        (sinℝ x Mul.· sinℝ x))
cosℝ-double≡one-sub-doubleSinSquare x =
    cosℝ-double x
  ∙ IdentityAlgebra.cosine-as-total-minus-double-sine
      ℝCommRing (cosℝ x) (sinℝ x)
  ∙ cong
      (λ total → total Group.-
        ((sinℝ x Mul.· sinℝ x) Add.+
          (sinℝ x Mul.· sinℝ x)))
      (cosSquare-add-sinSquare≡one x)


cosℝ-double≡doubleCosSquare-sub-one : ∀ x →
  cosℝ (x Add.+ x)
    ≡ ((cosℝ x Mul.· cosℝ x) Add.+
        (cosℝ x Mul.· cosℝ x)) Group.- Real.ιℚ 1
cosℝ-double≡doubleCosSquare-sub-one x =
    cosℝ-double x
  ∙ IdentityAlgebra.cosine-as-double-cosine-minus-total
      ℝCommRing (cosℝ x) (sinℝ x)
  ∙ cong
      (((cosℝ x Mul.· cosℝ x) Add.+
        (cosℝ x Mul.· cosℝ x)) Group.-_)
      (cosSquare-add-sinSquare≡one x)
