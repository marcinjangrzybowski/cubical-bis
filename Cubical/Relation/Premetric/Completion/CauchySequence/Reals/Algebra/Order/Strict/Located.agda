module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Located where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Rationals as ℚData
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue using (Dichotomyℚ)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Relation.Nullary

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.Relation.Binary.Base

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
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Addition
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Negation
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.AbsoluteValue
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Properties
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Density
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Metric.Distance
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Metric.Equality

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ


maxPositiveStrictUpper : ∀ x y z →
  x <ℝ z → y <ℝ z → (x ⊔ℝ y) <ℝ z
maxPositiveStrictUpper x y z = PT.map2 combine
  where
  combine : PositiveGap x z → PositiveGap y z →
    PositiveGap (x ⊔ℝ y) z
  combine u v = positiveGap κ
    (subst (_≤ℝ z)
      (sym (max-translate-right x y (Real.ιℚ (fst κ))))
      (max-least
        (x Add.+ Real.ιℚ (fst κ))
        (y Add.+ Real.ιℚ (fst κ)) z x+κ≤z y+κ≤z))
    where
    κ : ℚ₊
    κ = min₊ (width u) (width v)

    κ≤u : fst κ ℚ.≤ fst (width u)
    κ≤u = ℚ.min≤ (fst (width u)) (fst (width v))

    κ≤v : fst κ ℚ.≤ fst (width v)
    κ≤v = ℚ.min≤' (fst (width u)) (fst (width v))

    x+κ≤z : x Add.+ Real.ιℚ (fst κ) ≤ℝ z
    x+κ≤z =
      ≤ℝ-trans
        (x Add.+ Real.ιℚ (fst κ))
        (x Add.+ Real.ιℚ (fst (width u))) z
        (add-preserves≤-left
          (Real.ιℚ (fst κ)) (Real.ιℚ (fst (width u))) x
          (≤ℚ→≤ℝ (fst κ) (fst (width u)) κ≤u))
        (bound u)

    y+κ≤z : y Add.+ Real.ιℚ (fst κ) ≤ℝ z
    y+κ≤z =
      ≤ℝ-trans
        (y Add.+ Real.ιℚ (fst κ))
        (y Add.+ Real.ιℚ (fst (width v))) z
        (add-preserves≤-left
          (Real.ιℚ (fst κ)) (Real.ιℚ (fst (width v))) y
          (≤ℚ→≤ℝ (fst κ) (fst (width v)) κ≤v))
        (bound v)


minPositiveStrictLower : ∀ x y z →
  z <ℝ x → z <ℝ y → z <ℝ (x ⊓ℝ y)
minPositiveStrictLower x y z z≪x z≪y =
  subst (λ w → w <ℝ (x ⊓ℝ y))
    (Neg.neg-involutive z)
    (<ℝ-neg
      ((Neg.- x) ⊔ℝ (Neg.- y)) (Neg.- z)
      (maxPositiveStrictUpper
        (Neg.- x) (Neg.- y) (Neg.- z)
        (<ℝ-neg z x z≪x)
        (<ℝ-neg z y z≪y)))


-- Constructive locatedness: an exhibited gap from x to z decides, under
-- truncation, on which side of any y a positive gap remains.

positiveStrictDichotomy : ∀ x y z →
  x <ℝ z → ∥ (y <ℝ z) ⊎ (x <ℝ y) ∥₁
positiveStrictDichotomy x y z = PT.rec squash₁ dichotomyFromGap
  where
  dichotomyFromGap : PositiveGap x z →
    ∥ (y <ℝ z) ⊎ (x <ℝ y) ∥₁
  dichotomyFromGap w =
    PT.map2 compare
      (denseℚinℝ x (x Add.+ Real.ιℚ (fst half)) x≪x+half)
      (denseℚinℝ (y Group.- Real.ιℚ (fst half)) y y-half≪y)
    where
    δ : ℚ₊
    δ = width w

    half : ℚ₊
    half = δ /2₊

    x≪x+half : x <ℝ (x Add.+ Real.ιℚ (fst half))
    x≪x+half =
      subst (λ w → w <ℝ (x Add.+ Real.ιℚ (fst half)))
        (add-zero-right x)
        (<ℝ-add-left
          (Real.ιℚ 0) (Real.ιℚ (fst half)) x
          (<ℚ→<ℝ 0 (fst half) (snd half)))

    y-half≪y : (y Group.- Real.ιℚ (fst half)) <ℝ y
    y-half≪y =
      subst2 _<ℝ_
        (add-zero-right (y Group.- Real.ιℚ (fst half)))
        (sub-add-cancel y (Real.ιℚ (fst half)))
        (<ℝ-add-left
          (Real.ιℚ 0) (Real.ιℚ (fst half))
          (y Group.- Real.ιℚ (fst half))
          (<ℚ→<ℝ 0 (fst half) (snd half)))

    x+halvesPath :
      (x Add.+ Real.ιℚ (fst half)) Add.+ Real.ιℚ (fst half) ≡
      x Add.+ Real.ιℚ (fst δ)
    x+halvesPath =
        sym (add-assoc x (Real.ιℚ (fst half)) (Real.ιℚ (fst half)))
      ∙ cong (x Add.+_)
          (Add.add-ι-ι (fst half) (fst half)
          ∙ cong Real.ιℚ (/2+/2≡id (fst δ)))

    compare :
      (Σ[ a ∈ ℚData.ℚ ]
        (x <ℝ Real.ιℚ a) ×
        (Real.ιℚ a <ℝ x Add.+ Real.ιℚ (fst half))) →
      (Σ[ b ∈ ℚData.ℚ ]
        ((y Group.- Real.ιℚ (fst half)) <ℝ Real.ιℚ b) ×
        (Real.ιℚ b <ℝ y)) →
      (y <ℝ z) ⊎ (x <ℝ y)
    compare (a , x≪a , a≪x+half)
            (b , y-half≪b , b≪y) =
      ⊎.rec b≤aCase a<bCase (Dichotomyℚ b a)
      where
      b≤aCase : b ℚ.≤ a → (y <ℝ z) ⊎ (x <ℝ y)
      b≤aCase b≤a = inl
        (≪≤ℝ-trans y (x Add.+ Real.ιℚ (fst δ)) z
          y≪x+δ (bound w))
        where
        y-half≪x+half :
          (y Group.- Real.ιℚ (fst half))
            <ℝ (x Add.+ Real.ιℚ (fst half))
        y-half≪x+half =
          <ℝ-trans
            (y Group.- Real.ιℚ (fst half)) (Real.ιℚ a)
            (x Add.+ Real.ιℚ (fst half))
            (≪≤ℝ-trans
              (y Group.- Real.ιℚ (fst half)) (Real.ιℚ b) (Real.ιℚ a)
              y-half≪b (≤ℚ→≤ℝ b a b≤a))
            a≪x+half

        y≪x+δ : y <ℝ (x Add.+ Real.ιℚ (fst δ))
        y≪x+δ =
          subst2 _<ℝ_
            (sub-add-cancel y (Real.ιℚ (fst half)))
            x+halvesPath
            (<ℝ-add-right
              (y Group.- Real.ιℚ (fst half))
              (x Add.+ Real.ιℚ (fst half))
              (Real.ιℚ (fst half)) y-half≪x+half)

      a<bCase : a ℚ.< b → (y <ℝ z) ⊎ (x <ℝ y)
      a<bCase a<b = inr
        (<ℝ-trans x (Real.ιℚ b) y
          (<ℝ-trans x (Real.ιℚ a) (Real.ιℚ b)
            x≪a (<ℚ→<ℝ a b a<b))
          b≪y)


isWeaklyLinear<ℝ : BinaryRelation.isWeaklyLinear _<ℝ_
isWeaklyLinear<ℝ x y z x≪y =
  PT.map (⊎.rec inr inl)
    (positiveStrictDichotomy x z y x≪y)


-- Closed order is recovered from arbitrarily small positive slack.  The
-- positive part of x-y lies below every positive rational; the previously
-- proved order characterization of equality therefore makes it zero.

arbitrarilySmallPositiveSlack→≤ : ∀ x y →
  (∀ ε → x <ℝ (y Add.+ Real.ιℚ (fst ε))) → x ≤ℝ y
arbitrarilySmallPositiveSlack→≤ x y x≪y+ε =
  subst2 _≤ℝ_
    (sub-add-cancel x y) (add-zero-left y)
    (add-preserves≤-right (x Group.- y) (Real.ιℚ 0) y difference≤0)
  where
  difference : Real.ℝ
  difference = x Group.- y

  positivePart : Real.ℝ
  positivePart = difference ⊔ℝ Real.ιℚ 0

  cancelYPath : ∀ ε →
    (y Add.+ Real.ιℚ (fst ε)) Add.+ (Neg.- y) ≡ Real.ιℚ (fst ε)
  cancelYPath ε =
      sym (add-assoc y (Real.ιℚ (fst ε)) (Neg.- y))
    ∙ cong (y Add.+_) (add-comm (Real.ιℚ (fst ε)) (Neg.- y))
    ∙ add-assoc y (Neg.- y) (Real.ιℚ (fst ε))
    ∙ cong (Add._+ Real.ιℚ (fst ε)) (add-inverse-right y)
    ∙ add-zero-left (Real.ιℚ (fst ε))

  difference≤ε : ∀ ε → difference ≤ℝ Real.ιℚ (fst ε)
  difference≤ε ε =
    subst (difference ≤ℝ_) (cancelYPath ε)
      (add-preserves≤-right x
        (y Add.+ Real.ιℚ (fst ε)) (Neg.- y)
        (<ℝ-weaken x (y Add.+ Real.ιℚ (fst ε)) (x≪y+ε ε)))

  positivePart≤ε : ∀ ε → positivePart ≤ℝ Real.ιℚ (fst ε)
  positivePart≤ε ε =
    max-least difference (Real.ιℚ 0) (Real.ιℚ (fst ε))
      (difference≤ε ε)
      (≤ℚ→≤ℝ 0 (fst ε) (ℚ.<Weaken≤ 0 (fst ε) (snd ε)))

  zero≤positivePart : Real.ιℚ 0 ≤ℝ positivePart
  zero≤positivePart = max-upper-right difference (Real.ιℚ 0)

  negPositivePart≤zero : (Neg.- positivePart) ≤ℝ Real.ιℚ 0
  negPositivePart≤zero =
    subst ((Neg.- positivePart) ≤ℝ_) neg-zero
      (neg-reverses≤ (Real.ιℚ 0) positivePart zero≤positivePart)

  negPositivePart≤positivePart : (Neg.- positivePart) ≤ℝ positivePart
  negPositivePart≤positivePart =
    ≤ℝ-trans (Neg.- positivePart) (Real.ιℚ 0) positivePart
      negPositivePart≤zero zero≤positivePart

  absPositivePartPath : Abs.absℝ positivePart ≡ positivePart
  absPositivePartPath =
      abs-as-max positivePart
    ∙ max-comm positivePart (Neg.- positivePart)
    ∙ negPositivePart≤positivePart

  distancePositivePartZeroPath :
    distance positivePart (Real.ιℚ 0) ≡ positivePart
  distancePositivePartZeroPath =
      cong Abs.absℝ (sub-zero-right positivePart)
    ∙ absPositivePartPath

  positivePartDistanceSmall :
    OrderDistanceArbitrarilySmall positivePart (Real.ιℚ 0)
  positivePartDistanceSmall ε =
    subst (_≤ℝ Real.ιℚ (fst ε))
      (sym distancePositivePartZeroPath) (positivePart≤ε ε)

  positivePartIsZero : positivePart ≡ Real.ιℚ 0
  positivePartIsZero =
    orderDistanceArbitrarilySmall→equality positivePartDistanceSmall

  difference≤0 : difference ≤ℝ Real.ιℚ 0
  difference≤0 =
    subst (difference ≤ℝ_) positivePartIsZero
      (max-upper-left difference (Real.ιℚ 0))


≤ℝ→notPositiveGreater : ∀ x y →
  x ≤ℝ y → ¬ (y <ℝ x)
≤ℝ→notPositiveGreater x y x≤y y≪x =
  <ℝ-irrefl y (≪≤ℝ-trans y x y y≪x x≤y)

notPositiveGreater→≤ℝ : ∀ x y →
  ¬ (y <ℝ x) → x ≤ℝ y
notPositiveGreater→≤ℝ x y not-y≪x =
  arbitrarilySmallPositiveSlack→≤ x y slack
  where
  slack : ∀ ε → x <ℝ (y Add.+ Real.ιℚ (fst ε))
  slack ε =
    PT.rec
      (isProp<ℝ x (y Add.+ Real.ιℚ (fst ε)))
      (⊎.rec (idfun _) (⊥.rec ∘ not-y≪x))
      (positiveStrictDichotomy
        y x (y Add.+ Real.ιℚ (fst ε)) y≪y+ε)
    where
    y≪y+ε : y <ℝ (y Add.+ Real.ιℚ (fst ε))
    y≪y+ε =
      subst (λ w → w <ℝ (y Add.+ Real.ιℚ (fst ε)))
        (add-zero-right y)
        (<ℝ-add-left
          (Real.ιℚ 0) (Real.ιℚ (fst ε)) y
          (<ℚ→<ℝ 0 (fst ε) (snd ε)))


≤NotPositiveGreaterEquiv : ∀ x y →
  (x ≤ℝ y) ≃ (¬ (y <ℝ x))
≤NotPositiveGreaterEquiv x y =
  propBiimpl→Equiv
    (isProp≤ℝ x y) (isProp¬ (y <ℝ x))
    (≤ℝ→notPositiveGreater x y)
    (notPositiveGreater→≤ℝ x y)


positiveSum→positiveSummand : ∀ x y →
  Real.ιℚ 0 <ℝ (x Add.+ y) →
  ∥ (Real.ιℚ 0 <ℝ x) ⊎ (Real.ιℚ 0 <ℝ y) ∥₁
positiveSum→positiveSummand x y 0≪x+y =
  PT.map
    (⊎.rec (inr ∘ x≪x+y→0≪y) inl)
    (positiveStrictDichotomy (Real.ιℚ 0) x (x Add.+ y) 0≪x+y)
  where
  x≪x+y→0≪y : x <ℝ (x Add.+ y) → Real.ιℚ 0 <ℝ y
  x≪x+y→0≪y x≪x+y =
    <ℝ-add-left-cancel (Real.ιℚ 0) y x
      (subst (λ w → w <ℝ (x Add.+ y))
        (sym (add-zero-right x)) x≪x+y)
