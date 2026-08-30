module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Multiplication where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals.Base as ℚ
import Cubical.Data.Rationals.Order as ℚ

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Negation
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Properties
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Laws
  as MulL using (mul-comm)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.CommRing
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Multiplication


private
  module ℝRing = RingTheory (CommRing→Ring ℝCommRing)


mul-positive : ∀ x y →
  Real.ιℚ 0 <ℝ x → Real.ιℚ 0 <ℝ y →
  Real.ιℚ 0 <ℝ (x Mul.· y)
mul-positive x y =
  PT.rec2 (isProp<ℝ (Real.ιℚ 0) (x Mul.· y)) prove
  where
  prove :
    PositiveGap (Real.ιℚ 0) x →
    PositiveGap (Real.ιℚ 0) y →
    Real.ιℚ 0 <ℝ (x Mul.· y)
  prove gapx gapy = ∣ positiveGap δ·ε outputBound ∣₁
    where
    δ ε : ℚ₊
    δ = width gapx
    ε = width gapy

    δ·ε : ℚ₊
    δ·ε = δ ·₊ ε

    0≤ιδ : Real.ιℚ 0 ≤ℝ Real.ιℚ (fst δ)
    0≤ιδ = ≤ℚ→≤ℝ 0 (fst δ)
      (ℚ.<Weaken≤ 0 (fst δ) (snd δ))

    0≤ιε : Real.ιℚ 0 ≤ℝ Real.ιℚ (fst ε)
    0≤ιε = ≤ℚ→≤ℝ 0 (fst ε)
      (ℚ.<Weaken≤ 0 (fst ε) (snd ε))

    ιδ≤x : Real.ιℚ (fst δ) ≤ℝ x
    ιδ≤x = subst (_≤ℝ x)
      (add-zero-left (Real.ιℚ (fst δ))) (bound gapx)

    ιε≤y : Real.ιℚ (fst ε) ≤ℝ y
    ιε≤y = subst (_≤ℝ y)
      (add-zero-left (Real.ιℚ (fst ε))) (bound gapy)

    embeddedProduct≤ : Real.ιℚ (fst δ·ε) ≤ℝ (x Mul.· y)
    embeddedProduct≤ =
      subst (_≤ℝ (x Mul.· y))
        (Mul.mul-ι-ι (fst δ) (fst ε))
        (mul-monotone-nonnegative
          (Real.ιℚ (fst δ)) x (Real.ιℚ (fst ε)) y
          ιδ≤x ιε≤y 0≤ιδ 0≤ιε)

    outputBound :
      (Real.ιℚ 0 Add.+ Real.ιℚ (fst δ·ε)) ≤ℝ (x Mul.· y)
    outputBound = subst (_≤ℝ (x Mul.· y))
      (sym (add-zero-left (Real.ιℚ (fst δ·ε)))) embeddedProduct≤


mul-preserves≪-right-positive : ∀ x y z →
  x <ℝ y → Real.ιℚ 0 <ℝ z →
  (x Mul.· z) <ℝ (y Mul.· z)
mul-preserves≪-right-positive x y z x≪y 0≪z =
  strictlyPositiveDifference≪→<ℝ
    (x Mul.· z) (y Mul.· z)
    (subst (Real.ιℚ 0 <ℝ_)
      (ℝRing.·DistL- y x z)
      (mul-positive (y Group.- x) z
        (strictlyPositiveDifference≪ x y x≪y) 0≪z))


mul-preserves≪-left-positive : ∀ x y z →
  x <ℝ y → Real.ιℚ 0 <ℝ z →
  (z Mul.· x) <ℝ (z Mul.· y)
mul-preserves≪-left-positive x y z x≪y 0≪z =
  subst2 _<ℝ_ (MulL.mul-comm x z) (MulL.mul-comm y z)
    (mul-preserves≪-right-positive x y z x≪y 0≪z)
