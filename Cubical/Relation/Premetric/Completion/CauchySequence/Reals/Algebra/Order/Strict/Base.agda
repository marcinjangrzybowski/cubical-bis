module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Relation.Nullary
open import Cubical.Relation.Binary.Order.Quoset

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Base as ℚR
open import Cubical.Data.Rationals.Order.AbsoluteValue using
  (<→ℚ₊ ; Dichotomyℚ)
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Rationals.Order as ℚ

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Associativity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Addition

open PositiveRationals


-- Strict order is an exhibited positive rational gap.  This is the order
-- used by the completed ordered-ring structure.

record PositiveGap (x y : Real.ℝ) : Type where
  constructor positiveGap
  field
    width : ℚ₊
    bound : x Add.+ Real.ιℚ (fst width) ≤ℝ y

open PositiveGap public

infix 4 _<ℝ_

_<ℝ_ : Real.ℝ → Real.ℝ → Type
x <ℝ y = ∥ PositiveGap x y ∥₁

isProp<ℝ : ∀ x y → isProp (x <ℝ y)
isProp<ℝ _ _ = squash₁

private
  combineGapPath : ∀ x (δ ε : ℚ₊) →
    x Add.+ Real.ιℚ (fst (δ +₊ ε)) ≡
    (x Add.+ Real.ιℚ (fst δ)) Add.+ Real.ιℚ (fst ε)
  combineGapPath x δ ε =
      cong (x Add.+_) (sym (Add.add-ι-ι (fst δ) (fst ε)))
    ∙ add-assoc x (Real.ιℚ (fst δ)) (Real.ιℚ (fst ε))

<ℝ-weaken : ∀ x y → x <ℝ y → x ≤ℝ y
<ℝ-weaken x y =
  PT.rec (isProp≤ℝ x y) λ gap →
    ≤ℝ-trans x (x Add.+ Real.ιℚ (fst (width gap))) y
      (subst (_≤ℝ (x Add.+ Real.ιℚ (fst (width gap))))
        (add-zero-right x)
        (add-preserves≤-left
          (Real.ιℚ 0) (Real.ιℚ (fst (width gap))) x
          (≤ℚ→≤ℝ 0 (fst (width gap))
            (ℚ.<Weaken≤ 0 (fst (width gap)) (snd (width gap))))))
      (bound gap)

<ℝ-trans : ∀ x y z → x <ℝ y → y <ℝ z → x <ℝ z
<ℝ-trans x y z =
  PT.map2 λ left right →
    positiveGap (width left +₊ width right)
      (subst (_≤ℝ z) (sym (combineGapPath x (width left) (width right)))
        (≤ℝ-trans
          ((x Add.+ Real.ιℚ (fst (width left))) Add.+
            Real.ιℚ (fst (width right)))
          (y Add.+ Real.ιℚ (fst (width right))) z
          (add-preserves≤-right
            (x Add.+ Real.ιℚ (fst (width left))) y
            (Real.ιℚ (fst (width right))) (bound left))
          (bound right)))

≤<ℝ-trans : ∀ x y z → x ≤ℝ y → y <ℝ z → x <ℝ z
≤<ℝ-trans x y z x≤y =
  PT.map λ gap →
    positiveGap (width gap)
      (≤ℝ-trans
        (x Add.+ Real.ιℚ (fst (width gap)))
        (y Add.+ Real.ιℚ (fst (width gap))) z
        (add-preserves≤-right x y (Real.ιℚ (fst (width gap))) x≤y)
        (bound gap))

≪≤ℝ-trans : ∀ x y z → x <ℝ y → y ≤ℝ z → x <ℝ z
≪≤ℝ-trans x y z x≪y y≤z =
  PT.map
    (λ gap →
      positiveGap (width gap)
        (≤ℝ-trans
          (x Add.+ Real.ιℚ (fst (width gap))) y z
          (bound gap) y≤z))
    x≪y

<ℚ→<ℝ : ∀ p q → p ℚ.< q → Real.ιℚ p <ℝ Real.ιℚ q
<ℚ→<ℝ p q p<q =
  ∣ positiveGap δ
      (subst (_≤ℝ Real.ιℚ q) (sym gapPath) (≤ℝ-refl (Real.ιℚ q))) ∣₁
  where
  δ : ℚ₊
  δ = <→ℚ₊ p q p<q

  gapPath : Real.ιℚ p Add.+ Real.ιℚ (fst δ) ≡ Real.ιℚ q
  gapPath = Add.add-ι-ι p (fst δ) ∙ cong Real.ιℚ ℚ!


-- Reflection of rational order is equivalent to injectivity of the rational
-- embedding and to irreflexivity of the positive-gap order.  Closeness
-- supplies the injectivity premise.

RationalOrderReflection : Type
RationalOrderReflection = ∀ p q →
  Real.ιℚ p ≤ℝ Real.ιℚ q → p ℚ.≤ q

RationalInjectionInjective : Type
RationalInjectionInjective = ∀ p q →
  Real.ιℚ p ≡ Real.ιℚ q → p ≡ q

PositiveGapIrreflexive : Type
PositiveGapIrreflexive = ∀ x → ¬ (x <ℝ x)

isPropRationalOrderReflection : isProp RationalOrderReflection
isPropRationalOrderReflection =
  isPropΠ2 λ p q → isProp→ (ℚ.isProp≤ p q)

isPropRationalInjectionInjective : isProp RationalInjectionInjective
isPropRationalInjectionInjective =
  isPropΠ2 λ p q → isProp→ (ℚR.isSetℚ p q)

isPropPositiveGapIrreflexive : isProp PositiveGapIrreflexive
isPropPositiveGapIrreflexive =
  isPropΠ λ x → isProp¬ (x <ℝ x)

rationalInjection→orderReflection :
  RationalInjectionInjective → RationalOrderReflection
rationalInjection→orderReflection injective p q embedded≤ =
  subst (p ℚ.≤_)
    (injective (ℚ.max p q) q
      (sym (max-ι p q) ∙ embedded≤))
    (ℚ.≤max p q)

orderReflection→rationalInjection :
  RationalOrderReflection → RationalInjectionInjective
orderReflection→rationalInjection reflects p q embeddedPath =
  ℚ.isAntisym≤ p q
    (reflects p q
      (subst (Real.ιℚ p ≤ℝ_) embeddedPath (≤ℝ-refl (Real.ιℚ p))))
    (reflects q p
      (subst (_≤ℝ Real.ιℚ p) embeddedPath (≤ℝ-refl (Real.ιℚ p))))

rationalInjection≃orderReflection :
  RationalInjectionInjective ≃ RationalOrderReflection
rationalInjection≃orderReflection =
  propBiimpl→Equiv
    isPropRationalInjectionInjective
    isPropRationalOrderReflection
    rationalInjection→orderReflection
    orderReflection→rationalInjection

orderReflection→positiveGapIrreflexive :
  RationalOrderReflection → PositiveGapIrreflexive
orderReflection→positiveGapIrreflexive reflects x =
  PT.rec isProp⊥ λ gap →
    ℚ.isIrrefl< 0
      (ℚ.isTrans<≤ 0 (fst (width gap)) 0
        (snd (width gap))
        (reflects (fst (width gap)) 0
          (add-reflects≤-left
            (Real.ιℚ (fst (width gap))) (Real.ιℚ 0) x
            (subst ((x Add.+ Real.ιℚ (fst (width gap))) ≤ℝ_)
              (sym (add-zero-right x)) (bound gap)))))

positiveGapIrreflexive→orderReflection :
  PositiveGapIrreflexive → RationalOrderReflection
positiveGapIrreflexive→orderReflection irrefl p q embedded≤ =
  ⊎.rec
    (idfun (p ℚ.≤ q))
    (λ q<p → ⊥.rec
      (irrefl (Real.ιℚ q)
        (≪≤ℝ-trans (Real.ιℚ q) (Real.ιℚ p) (Real.ιℚ q)
          (<ℚ→<ℝ q p q<p) embedded≤)))
    (Dichotomyℚ p q)

positiveGapIrreflexive≃orderReflection :
  PositiveGapIrreflexive ≃ RationalOrderReflection
positiveGapIrreflexive≃orderReflection =
  propBiimpl→Equiv
    isPropPositiveGapIrreflexive
    isPropRationalOrderReflection
    positiveGapIrreflexive→orderReflection
    orderReflection→positiveGapIrreflexive

orderReflection→positiveGapIsQuoset :
  RationalOrderReflection → IsQuoset _<ℝ_
orderReflection→positiveGapIsQuoset reflects
  .IsQuoset.is-set = Real.Base.isSetCompletion
orderReflection→positiveGapIsQuoset reflects
  .IsQuoset.is-prop-valued = isProp<ℝ
orderReflection→positiveGapIsQuoset reflects
  .IsQuoset.is-irrefl = orderReflection→positiveGapIrreflexive reflects
orderReflection→positiveGapIsQuoset reflects
  .IsQuoset.is-trans = <ℝ-trans
orderReflection→positiveGapIsQuoset reflects
  .IsQuoset.is-asym = λ x y x≪y y≪x →
    orderReflection→positiveGapIrreflexive reflects x
      (<ℝ-trans x y x x≪y y≪x)

rationalInjectionIsInjective : RationalInjectionInjective
rationalInjectionIsInjective = Real.rationalInjectionInjective

rationalOrderReflects : RationalOrderReflection
rationalOrderReflects =
  rationalInjection→orderReflection rationalInjectionIsInjective

positiveGapIrreflexive : PositiveGapIrreflexive
positiveGapIrreflexive =
  orderReflection→positiveGapIrreflexive rationalOrderReflects

positiveGapIsQuoset : IsQuoset _<ℝ_
positiveGapIsQuoset =
  orderReflection→positiveGapIsQuoset rationalOrderReflects
