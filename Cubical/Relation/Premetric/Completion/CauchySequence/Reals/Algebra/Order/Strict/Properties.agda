module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function

open import Cubical.Data.Rationals as ℚR
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Relation.Nullary

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

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
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.GroupLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Addition
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base

open PositiveRationals


-- The exhibited-positive-gap relation has the usual strict-order algebra.

<ℝ-irrefl : ∀ x → ¬ (x <ℝ x)
<ℝ-irrefl = positiveGapIrreflexive

<ℝ-asym : ∀ x y → x <ℝ y → ¬ (y <ℝ x)
<ℝ-asym x y x≪y y≪x =
  <ℝ-irrefl x (<ℝ-trans x y x x≪y y≪x)

private
  translateGapPath : ∀ x z (δ : ℚ₊) →
    (x Add.+ z) Add.+ Real.ιℚ (fst δ) ≡
    (x Add.+ Real.ιℚ (fst δ)) Add.+ z
  translateGapPath x z δ =
      sym (add-assoc x z (Real.ιℚ (fst δ)))
    ∙ cong (x Add.+_) (add-comm z (Real.ιℚ (fst δ)))
    ∙ add-assoc x (Real.ιℚ (fst δ)) z


<ℝ-add-right : ∀ x y z →
  x <ℝ y → (x Add.+ z) <ℝ (y Add.+ z)
<ℝ-add-right x y z = PT.map λ gap →
  positiveGap (width gap)
    (subst (_≤ℝ (y Add.+ z))
      (sym (translateGapPath x z (width gap)))
      (add-preserves≤-right
        (x Add.+ Real.ιℚ (fst (width gap))) y z (bound gap)))

<ℝ-add-right-cancel : ∀ x y z →
  (x Add.+ z) <ℝ (y Add.+ z) → x <ℝ y
<ℝ-add-right-cancel x y z = PT.map λ gap →
  positiveGap (width gap)
    (add-reflects≤-right
      (x Add.+ Real.ιℚ (fst (width gap))) y z
      (subst (_≤ℝ (y Add.+ z))
        (translateGapPath x z (width gap)) (bound gap)))

<ℝ-add-left : ∀ x y z →
  x <ℝ y → (z Add.+ x) <ℝ (z Add.+ y)
<ℝ-add-left x y z x≪y =
  subst2 _<ℝ_ (add-comm x z) (add-comm y z)
    (<ℝ-add-right x y z x≪y)

<ℝ-add-left-cancel : ∀ x y z →
  (z Add.+ x) <ℝ (z Add.+ y) → x <ℝ y
<ℝ-add-left-cancel x y z translated =
  <ℝ-add-right-cancel x y z
    (subst2 _<ℝ_ (add-comm z x) (add-comm z y) translated)

addRightPositiveStrictOrderEquiv : ∀ x y z →
  ((x Add.+ z) <ℝ (y Add.+ z)) ≃ (x <ℝ y)
addRightPositiveStrictOrderEquiv x y z =
  propBiimpl→Equiv
    (isProp<ℝ (x Add.+ z) (y Add.+ z)) (isProp<ℝ x y)
    (<ℝ-add-right-cancel x y z) (<ℝ-add-right x y z)

addLeftPositiveStrictOrderEquiv : ∀ x y z →
  ((z Add.+ x) <ℝ (z Add.+ y)) ≃ (x <ℝ y)
addLeftPositiveStrictOrderEquiv x y z =
  propBiimpl→Equiv
    (isProp<ℝ (z Add.+ x) (z Add.+ y)) (isProp<ℝ x y)
    (<ℝ-add-left-cancel x y z) (<ℝ-add-left x y z)


<ℝ-add : ∀ x y z w →
  x <ℝ y → z <ℝ w →
  (x Add.+ z) <ℝ (y Add.+ w)
<ℝ-add x y z w x≪y z≪w =
  <ℝ-trans (x Add.+ z) (y Add.+ z) (y Add.+ w)
    (<ℝ-add-right x y z x≪y)
    (<ℝ-add-left z w y z≪w)

≤<ℝ-add : ∀ x y z w →
  x ≤ℝ y → z <ℝ w →
  (x Add.+ z) <ℝ (y Add.+ w)
≤<ℝ-add x y z w x≤y z≪w =
  ≤<ℝ-trans (x Add.+ z) (y Add.+ z) (y Add.+ w)
    (add-preserves≤-right x y z x≤y)
    (<ℝ-add-left z w y z≪w)

≪≤ℝ-add : ∀ x y z w →
  x <ℝ y → z ≤ℝ w →
  (x Add.+ z) <ℝ (y Add.+ w)
≪≤ℝ-add x y z w x≪y z≤w =
  ≪≤ℝ-trans (x Add.+ z) (y Add.+ z) (y Add.+ w)
    (<ℝ-add-right x y z x≪y)
    (add-preserves≤-left z w y z≤w)


strictlyPositiveDifference≪ : ∀ x y →
  x <ℝ y → Real.ιℚ 0 <ℝ (y Group.- x)
strictlyPositiveDifference≪ x y x≪y =
  subst2 _<ℝ_
    (add-inverse-right x) refl
    (<ℝ-add-right x y (Neg.- x) x≪y)

strictlyPositiveDifference≪→<ℝ : ∀ x y →
  Real.ιℚ 0 <ℝ (y Group.- x) → x <ℝ y
strictlyPositiveDifference≪→<ℝ x y 0≪y-x =
  subst2 _<ℝ_
    (add-zero-left x) (sub-add-cancel y x)
    (<ℝ-add-right (Real.ιℚ 0) (y Group.- x) x 0≪y-x)

positiveStrictOrderDifferenceEquiv : ∀ x y →
  (x <ℝ y) ≃ (Real.ιℚ 0 <ℝ (y Group.- x))
positiveStrictOrderDifferenceEquiv x y =
  propBiimpl→Equiv
    (isProp<ℝ x y) (isProp<ℝ (Real.ιℚ 0) (y Group.- x))
    (strictlyPositiveDifference≪ x y)
    (strictlyPositiveDifference≪→<ℝ x y)


private
  negatedDifferencePath : ∀ x y →
    (Neg.- x) Group.- (Neg.- y) ≡ y Group.- x
  negatedDifferencePath x y =
      cong ((Neg.- x) Add.+_) (Neg.neg-involutive y)
    ∙ add-comm (Neg.- x) y


<ℝ-neg : ∀ x y → x <ℝ y → (Neg.- y) <ℝ (Neg.- x)
<ℝ-neg x y x≪y =
  strictlyPositiveDifference≪→<ℝ (Neg.- y) (Neg.- x)
    (subst (Real.ιℚ 0 <ℝ_)
      (sym (negatedDifferencePath x y))
      (strictlyPositiveDifference≪ x y x≪y))

neg-<ℝ : ∀ x y → (Neg.- y) <ℝ (Neg.- x) → x <ℝ y
neg-<ℝ x y =
  subst2 _<ℝ_ (Neg.neg-involutive x) (Neg.neg-involutive y)
  ∘ <ℝ-neg (Neg.- y) (Neg.- x)

negPositiveStrictOrderEquiv : ∀ x y →
  ((Neg.- y) <ℝ (Neg.- x)) ≃ (x <ℝ y)
negPositiveStrictOrderEquiv x y =
  propBiimpl→Equiv
    (isProp<ℝ (Neg.- y) (Neg.- x)) (isProp<ℝ x y)
    (neg-<ℝ x y) (<ℝ-neg x y)


<ℝ→<ℚ : ∀ p q → Real.ιℚ p <ℝ Real.ιℚ q → p ℚ.< q
<ℝ→<ℚ p q = PT.rec (ℚ.isProp< p q) prove
  where
  prove : PositiveGap (Real.ιℚ p) (Real.ιℚ q) → p ℚ.< q
  prove gap =
    ℚ.isTrans<≤ p pPlusδ q p<pPlusδ embeddedBound
    where
    pPlusδ : ℚR.ℚ
    pPlusδ = p ℚR.+ fst (width gap)

    p<pPlusδ : p ℚ.< pPlusδ
    p<pPlusδ =
      subst2 ℚ._<_
        (ℚR.+IdL p) (ℚR.+Comm (fst (width gap)) p)
        (ℚ.<-+o 0 (fst (width gap)) p (snd (width gap)))

    embeddedBound : pPlusδ ℚ.≤ q
    embeddedBound = rationalOrderReflects
      pPlusδ q
      (subst (_≤ℝ Real.ιℚ q)
        (Add.add-ι-ι p (fst (width gap))) (bound gap))

rationalPositiveStrictOrderEquiv : ∀ p q →
  (Real.ιℚ p <ℝ Real.ιℚ q) ≃ (p ℚ.< q)
rationalPositiveStrictOrderEquiv p q =
  propBiimpl→Equiv
    (isProp<ℝ (Real.ιℚ p) (Real.ιℚ q)) (ℚ.isProp< p q)
    (<ℝ→<ℚ p q) (<ℚ→<ℝ p q)
