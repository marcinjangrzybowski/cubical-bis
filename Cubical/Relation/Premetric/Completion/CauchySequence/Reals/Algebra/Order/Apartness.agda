module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Apartness where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Rationals.Base as ℚData
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Sum.Properties using (isProp⊎)

open import Cubical.Relation.Nullary

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.GroupLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.AbsoluteValue
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Properties


-- Constructive inequality is apartness, not the negation of equality.  Its
-- two branches retain the side of the exhibited positive gap.

infix 4 _＃_

_＃_ : Real.ℝ → Real.ℝ → Type
x ＃ y = (x <ℝ y) ⊎ (y <ℝ x)


isProp＃ : ∀ x y → isProp (x ＃ y)
isProp＃ x y =
  isProp⊎
    (isProp<ℝ x y) (isProp<ℝ y x) (<ℝ-asym x y)


ℝ₋₊ : Type
ℝ₋₊ = Σ[ x ∈ Real.ℝ ] Real.ιℚ 0 ＃ x


ℝ₋₊≡ : ∀ {x y : ℝ₋₊} → fst x ≡ fst y → x ≡ y
ℝ₋₊≡ = Σ≡Prop (isProp＃ (Real.ιℚ 0))


0＃ₚ : Real.ℝ → hProp ℓ-zero
0＃ₚ x = (Real.ιℚ 0 ＃ x) , isProp＃ (Real.ιℚ 0) x


rationalApartness : ∀ p q →
  (Real.ιℚ p ＃ Real.ιℚ q) ≃ (p ℚ.# q)
rationalApartness p q =
  propBiimpl→Equiv
    (isProp＃ (Real.ιℚ p) (Real.ιℚ q))
    (ℚ.isProp# p q)
    (⊎.map (<ℝ→<ℚ p q) (<ℝ→<ℚ q p))
    (⊎.map (<ℚ→<ℝ p q) (<ℚ→<ℝ q p))


apart-sym : ∀ x y → x ＃ y → y ＃ x
apart-sym _ _ = ⊎.rec inr inl


apart-irrefl : ∀ x → ¬ (x ＃ x)
apart-irrefl x = ⊎.rec (<ℝ-irrefl x) (<ℝ-irrefl x)


apart→notEqual : ∀ x y → x ＃ y → ¬ (x ≡ y)
apart→notEqual x y x＃y x≡y =
  apart-irrefl x (subst (x ＃_) (sym x≡y) x＃y)


apart-add-right : ∀ x y z →
  x ＃ y → (x Add.+ z) ＃ (y Add.+ z)
apart-add-right x y z =
  ⊎.map (<ℝ-add-right x y z) (<ℝ-add-right y x z)


apart-add-right-cancel : ∀ x y z →
  (x Add.+ z) ＃ (y Add.+ z) → x ＃ y
apart-add-right-cancel x y z =
  ⊎.map
    (<ℝ-add-right-cancel x y z)
    (<ℝ-add-right-cancel y x z)


addRightApartnessEquiv : ∀ x y z →
  ((x Add.+ z) ＃ (y Add.+ z)) ≃ (x ＃ y)
addRightApartnessEquiv x y z =
  propBiimpl→Equiv
    (isProp＃ (x Add.+ z) (y Add.+ z)) (isProp＃ x y)
    (apart-add-right-cancel x y z) (apart-add-right x y z)


apart-neg : ∀ x y → x ＃ y → (Neg.- x) ＃ (Neg.- y)
apart-neg x y =
  ⊎.rec (inr ∘ <ℝ-neg x y) (inl ∘ <ℝ-neg y x)


apart→zeroApartDifference : ∀ x y →
  x ＃ y → Real.ιℚ 0 ＃ (x Group.- y)
apart→zeroApartDifference x y = ⊎.rec
  (λ x<y → inr
    (subst ((x Group.- y) <ℝ_)
      (sub-self y)
      (<ℝ-add-right x y (Neg.- y) x<y)))
  (λ y<x → inl
    (subst (_<ℝ (x Group.- y))
      (sub-self y)
      (<ℝ-add-right y x (Neg.- y) y<x)))


zeroApartDifference→apart : ∀ x y →
  Real.ιℚ 0 ＃ (x Group.- y) → x ＃ y
zeroApartDifference→apart x y = ⊎.rec
  (λ 0<x-y → inr
    (subst2 _<ℝ_
      (add-zero-left y)
      (sub-add-cancel x y)
      (<ℝ-add-right (Real.ιℚ 0) (x Group.- y) y 0<x-y)))
  (λ x-y<0 → inl
    (subst2 _<ℝ_
      (sub-add-cancel x y)
      (add-zero-left y)
      (<ℝ-add-right (x Group.- y) (Real.ιℚ 0) y x-y<0)))


apartDifferenceEquiv : ∀ x y →
  (x ＃ y) ≃ (Real.ιℚ 0 ＃ (x Group.- y))
apartDifferenceEquiv x y =
  propBiimpl→Equiv
    (isProp＃ x y) (isProp＃ (Real.ιℚ 0) (x Group.- y))
    (apart→zeroApartDifference x y)
    (zeroApartDifference→apart x y)


positive→positiveAbs : ∀ z →
  Real.ιℚ 0 <ℝ z → Real.ιℚ 0 <ℝ Abs.absℝ z
positive→positiveAbs z 0<z =
  ≪≤ℝ-trans (Real.ιℚ 0) z (Abs.absℝ z) 0<z (x≤abs z)


negative→positiveAbs : ∀ z →
  z <ℝ Real.ιℚ 0 → Real.ιℚ 0 <ℝ Abs.absℝ z
negative→positiveAbs z z<0 =
  ≪≤ℝ-trans (Real.ιℚ 0) (Neg.- z) (Abs.absℝ z)
    0<-z (neg-x≤abs z)
  where
  0<-z : Real.ιℚ 0 <ℝ (Neg.- z)
  0<-z =
    subst2 _<ℝ_ neg-zero refl (<ℝ-neg z (Real.ιℚ 0) z<0)


apart→positiveAbsDifference : ∀ x y →
  x ＃ y → Real.ιℚ 0 <ℝ Abs.absℝ (x Group.- y)
apart→positiveAbsDifference x y x＃y =
  ⊎.rec
    (positive→positiveAbs (x Group.- y))
    (negative→positiveAbs (x Group.- y))
    (apart→zeroApartDifference x y x＃y)
