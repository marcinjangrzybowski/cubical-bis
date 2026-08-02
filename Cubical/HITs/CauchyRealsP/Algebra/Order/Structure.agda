module Cubical.HITs.CauchyRealsP.Algebra.Order.Structure where

open import Cubical.Foundations.Prelude

open import Cubical.Data.NatPlusOne

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.OrderedCommRing

open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Order.Poset
open import Cubical.Relation.Binary.Order.Pseudolattice
open import Cubical.Relation.Binary.Order.StrictOrder

open import Cubical.HITs.CauchyRealsP.Foundation
open import Cubical.HITs.CauchyRealsP.Algebra.Addition
open import Cubical.HITs.CauchyRealsP.Algebra.AdditionLaws
open import Cubical.HITs.CauchyRealsP.Algebra.Negation
open import Cubical.HITs.CauchyRealsP.Algebra.AdditiveGroup
open import Cubical.HITs.CauchyRealsP.Algebra.Lattice
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Base
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Addition
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Strict
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Located
open import Cubical.HITs.CauchyRealsP.Algebra.Order.Multiplication
open import Cubical.HITs.CauchyRealsP.Algebra.Multiplication.Base
open import Cubical.HITs.CauchyRealsP.Algebra.CommRing

ℝ≤Pseudolattice : Pseudolattice ℓ-zero ℓ-zero
ℝ≤Pseudolattice =
  makePseudolatticeFromPoset
    ℝ≤Poset minℝ maxℝ
    (λ {a b} → min≤left a b)
    (λ {a b} → min≤right a b)
    (λ {a b x} → ≤min x a b)
    (λ {a b} → left≤max a b)
    (λ {a b} → right≤max a b)
    (λ {a b x} → max≤ a b x)

isStrictOrderℝ : IsStrictOrder _<ℝ_
isStrictOrderℝ .IsStrictOrder.is-set = isSetℝ
isStrictOrderℝ .IsStrictOrder.is-prop-valued = isProp<ℝ
isStrictOrderℝ .IsStrictOrder.is-irrefl = <ℝ-irrefl
isStrictOrderℝ .IsStrictOrder.is-trans = <ℝ-trans
isStrictOrderℝ .IsStrictOrder.is-asym = <ℝ-asym
isStrictOrderℝ .IsStrictOrder.is-weakly-linear =
  isWeaklyLinear<ℝ

ℝ<StrictOrder : StrictOrder ℓ-zero ℓ-zero
ℝ<StrictOrder = strictorder ℝ _<ℝ_ isStrictOrderℝ

isOrderedCommRingℝ :
  IsOrderedCommRing
    0 1 _+_ _·_ -_ _<ℝ_ _≤ℝ_
isOrderedCommRingℝ .IsOrderedCommRing.isCommRing =
  CommRingStr.isCommRing (snd ℝCommRing)
isOrderedCommRingℝ .IsOrderedCommRing.isPseudolattice =
  PseudolatticeStr.is-pseudolattice (snd ℝ≤Pseudolattice)
isOrderedCommRingℝ .IsOrderedCommRing.isStrictOrder =
  isStrictOrderℝ
isOrderedCommRingℝ .IsOrderedCommRing.<-≤-weaken =
  <ℝ-weaken
isOrderedCommRingℝ .IsOrderedCommRing.≤≃¬> =
  ≤notGreaterEquiv
isOrderedCommRingℝ .IsOrderedCommRing.+MonoR≤ =
  ≤ℝ-addR
isOrderedCommRingℝ .IsOrderedCommRing.+MonoR< =
  <ℝ-addR
isOrderedCommRingℝ .IsOrderedCommRing.posSum→pos∨pos =
  positiveSum→positiveSummand
isOrderedCommRingℝ .IsOrderedCommRing.<-≤-trans =
  <≤ℝ-trans
isOrderedCommRingℝ .IsOrderedCommRing.≤-<-trans =
  ≤<ℝ-trans
isOrderedCommRingℝ .IsOrderedCommRing.·MonoR≤ =
  mulMonoR≤
isOrderedCommRingℝ .IsOrderedCommRing.·MonoR< =
  mulMonoR<
isOrderedCommRingℝ .IsOrderedCommRing.0<1 =
  <ℚ→<ℝ 0 1 (ℚ.0<pos 0 1)

ℝOrderedCommRing : OrderedCommRing ℓ-zero ℓ-zero
fst ℝOrderedCommRing = ℝ
OrderedCommRingStr.0r (snd ℝOrderedCommRing) = 0
OrderedCommRingStr.1r (snd ℝOrderedCommRing) = 1
OrderedCommRingStr._+_ (snd ℝOrderedCommRing) = _+_
OrderedCommRingStr._·_ (snd ℝOrderedCommRing) = _·_
OrderedCommRingStr.-_ (snd ℝOrderedCommRing) = -_
OrderedCommRingStr._<_ (snd ℝOrderedCommRing) = _<ℝ_
OrderedCommRingStr._≤_ (snd ℝOrderedCommRing) = _≤ℝ_
OrderedCommRingStr.isOrderedCommRing (snd ℝOrderedCommRing) =
  isOrderedCommRingℝ

ratIsOrderedCommRingHom :
  IsOrderedCommRingHom
    (snd ℚOrderedCommRing) rat
    (snd ℝOrderedCommRing)
ratIsOrderedCommRingHom =
  makeIsOrderedCommRingHom
    refl
    (λ q r → sym (rat+rat q r))
    (λ q r → sym (mul-rat q r))
    (<ℝ→<ℚ)

ratOrderedCommRingHom :
  OrderedCommRingHom ℚOrderedCommRing ℝOrderedCommRing
ratOrderedCommRingHom = rat , ratIsOrderedCommRingHom
