module Cubical.HITs.CauchyRealsP.Algebra.Order.Apartness where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset

open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎

open import Cubical.Relation.Nullary

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra.Addition
open import Cubical.HITs.CauchyRealsP.Algebra.AdditionLaws
open import Cubical.HITs.CauchyRealsP.Algebra.Negation
open import Cubical.HITs.CauchyRealsP.Algebra.AdditiveGroup
open import Cubical.HITs.CauchyRealsP.Algebra.AdditiveGroupLaws
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Base
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Strict
open import Cubical.HITs.CauchyRealsP.Algebra.Order.AbsoluteValue

infix 4 _＃_

_＃_ : ℝ → ℝ → Type
x ＃ y = (x <ℝ y) ⊎ (y <ℝ x)

isProp＃ : ∀ x y → isProp (x ＃ y)
isProp＃ x y =
  isProp⊎
    (isProp<ℝ x y)
    (isProp<ℝ y x)
    (<ℝ-asym x y)

ℝ₋₊ : Type
ℝ₋₊ = Σ ℝ (0 ＃_)

ℝ₋₊≡ : ∀ {x y : ℝ₋₊} → fst x ≡ fst y → x ≡ y
ℝ₋₊≡ = Σ≡Prop (isProp＃ 0)

0＃ₚ : ℝ → hProp ℓ-zero
0＃ₚ x = (0 ＃ x) , isProp＃ 0 x

rat＃ : ∀ p q → (rat p ＃ rat q) ≃ (p ℚ.# q)
rat＃ p q =
  propBiimpl→Equiv
    (isProp＃ (rat p) (rat q))
    (ℚ.isProp# p q)
    (⊎.map (<ℝ→<ℚ p q) (<ℝ→<ℚ q p))
    (⊎.map (<ℚ→<ℝ p q) (<ℚ→<ℝ q p))

apartSym : ∀ x y → x ＃ y → y ＃ x
apartSym _ _ = ⊎.rec inr inl

apartIrrefl : ∀ x → ¬ x ＃ x
apartIrrefl x = ⊎.rec (<ℝ-irrefl x) (<ℝ-irrefl x)

apart→notEqual : ∀ x y → x ＃ y → ¬ x ≡ y
apart→notEqual x y x＃y x≡y =
  apartIrrefl x (subst (x ＃_) (sym x≡y) x＃y)

apartAddR : ∀ x y z → x ＃ y → x + z ＃ y + z
apartAddR x y z =
  ⊎.map
    (<ℝ-addR x y z)
    (<ℝ-addR y x z)

apartAddR-cancel : ∀ x y z → x + z ＃ y + z → x ＃ y
apartAddR-cancel x y z =
  ⊎.map
    (<ℝ-addR-cancel x y z)
    (<ℝ-addR-cancel y x z)

addRApartEquiv : ∀ x y z → (x + z ＃ y + z) ≃ (x ＃ y)
addRApartEquiv x y z =
  propBiimpl→Equiv
    (isProp＃ (x + z) (y + z))
    (isProp＃ x y)
    (apartAddR-cancel x y z)
    (apartAddR x y z)

apartNeg : ∀ x y → x ＃ y → (- x) ＃ (- y)
apartNeg x y =
  ⊎.rec
    (inr ∘ <ℝ-neg x y)
    (inl ∘ <ℝ-neg y x)

apart→zeroApartDifference : ∀ x y → x ＃ y → 0 ＃ (x - y)
apart→zeroApartDifference x y =
  ⊎.rec
    (λ x<y →
      inr
        (subst ((x - y) <ℝ_)
          (subSelf y)
          (<ℝ-addR x y (- y) x<y)))
    (λ y<x →
      inl
        (subst (_<ℝ (x - y))
          (subSelf y)
          (<ℝ-addR y x (- y) y<x)))

zeroApartDifference→apart : ∀ x y → 0 ＃ (x - y) → x ＃ y
zeroApartDifference→apart x y =
  ⊎.rec
    (λ 0<x-y →
      inr
        (subst2 _<ℝ_
          (addIdL y)
          (subAddCancel x y)
          (<ℝ-addR 0 (x - y) y 0<x-y)))
    (λ x-y<0 →
      inl
        (subst2 _<ℝ_
          (subAddCancel x y)
          (addIdL y)
          (<ℝ-addR (x - y) 0 y x-y<0)))

apartDifferenceEquiv : ∀ x y → (x ＃ y) ≃ (0 ＃ (x - y))
apartDifferenceEquiv x y =
  propBiimpl→Equiv
    (isProp＃ x y)
    (isProp＃ 0 (x - y))
    (apart→zeroApartDifference x y)
    (zeroApartDifference→apart x y)

positive→positiveAbs : ∀ z →
  0 <ℝ z → 0 <ℝ absℝ z
positive→positiveAbs z 0<z =
  <≤ℝ-trans 0 z (absℝ z) 0<z (leAbs z)

negative→positiveAbs : ∀ z →
  z <ℝ 0 → 0 <ℝ absℝ z
negative→positiveAbs z z<0 =
  <≤ℝ-trans 0 (- z) (absℝ z)
    0<-z (negLeAbs z)
  where
  0<-z : 0 <ℝ (- z)
  0<-z =
    subst2 _<ℝ_ negZero refl
      (<ℝ-neg z 0 z<0)

apart→positiveAbsDifference : ∀ x y →
  x ＃ y → 0 <ℝ absℝ (x - y)
apart→positiveAbsDifference x y x＃y =
  ⊎.rec
    (positive→positiveAbs (x - y))
    (negative→positiveAbs (x - y))
    (apart→zeroApartDifference x y x＃y)
