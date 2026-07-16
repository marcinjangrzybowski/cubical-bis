module Cubical.HITs.CauchyReals.Algebra.Order.Instance where

open import Cubical.Foundations.Prelude

open import Cubical.Algebra.CommRing.Base
open import Cubical.Algebra.OrderedCommRing.Base

open import Cubical.Relation.Binary
open import Cubical.Relation.Binary.Order.Poset
open import Cubical.Relation.Binary.Order.Pseudolattice
open import Cubical.Relation.Binary.Order.StrictOrder

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Inverse
open import Cubical.HITs.CauchyReals.Algebra.Order.Properties

private
  module ℝCR = CommRingStr (snd ℝcommRing)


ℝ≤Poset : Poset ℓ-zero ℓ-zero
ℝ≤Poset = poset ℝ _≤ᵣ_ isPosetℝ


ℝ≤Pseudolattice : Pseudolattice ℓ-zero ℓ-zero
ℝ≤Pseudolattice =
  makePseudolatticeFromPoset ℝ≤Poset minᵣ maxᵣ
    (λ {a b} → min≤ᵣ a b)
    (λ {a b} → min≤ᵣ' a b)
    (λ {a b x} → ≤min-lem x a b)
    (λ {a b} → ≤maxᵣ a b)
    (λ {a b} → subst (b ≤ᵣ_) (maxᵣComm b a) (≤maxᵣ b a))
    (λ {a b x} → max≤-lem a b x)


isStrictOrderℝ : IsStrictOrder _<ᵣ_
isStrictOrderℝ .IsStrictOrder.is-set = isSetℝ
isStrictOrderℝ .IsStrictOrder.is-prop-valued = isProp<ᵣ
isStrictOrderℝ .IsStrictOrder.is-irrefl = isIrrefl<ᵣ
isStrictOrderℝ .IsStrictOrder.is-trans = isTrans<ᵣ
isStrictOrderℝ .IsStrictOrder.is-asym = isAsym<ᵣ
isStrictOrderℝ .IsStrictOrder.is-weakly-linear = isWeaklyLinear<ᵣ


ℝ<StrictOrder : StrictOrder ℓ-zero ℓ-zero
ℝ<StrictOrder = strictorder ℝ _<ᵣ_ isStrictOrderℝ


isOrderedCommRingℝ :
  IsOrderedCommRing ℝCR.0r ℝCR.1r _+ᵣ_ _·ᵣ_ -ᵣ_ _<ᵣ_ _≤ᵣ_
isOrderedCommRingℝ .IsOrderedCommRing.isCommRing =
  CommRingStr.isCommRing (snd ℝcommRing)
isOrderedCommRingℝ .IsOrderedCommRing.isPseudolattice =
  PseudolatticeStr.is-pseudolattice (snd ℝ≤Pseudolattice)
isOrderedCommRingℝ .IsOrderedCommRing.isStrictOrder = isStrictOrderℝ
isOrderedCommRingℝ .IsOrderedCommRing.<-≤-weaken = <ᵣWeaken≤ᵣ
isOrderedCommRingℝ .IsOrderedCommRing.≤≃¬> = ≤ᵣ≃≯ᵣ
isOrderedCommRingℝ .IsOrderedCommRing.+MonoR≤ = ≤ᵣ-+o
isOrderedCommRingℝ .IsOrderedCommRing.+MonoR< = <ᵣ-+o
isOrderedCommRingℝ .IsOrderedCommRing.posSum→pos∨pos = posSum→pos∨posᵣ
isOrderedCommRingℝ .IsOrderedCommRing.<-≤-trans = isTrans<≤ᵣ
isOrderedCommRingℝ .IsOrderedCommRing.≤-<-trans = isTrans≤<ᵣ
isOrderedCommRingℝ .IsOrderedCommRing.·MonoR≤ = ≤ᵣ-·ᵣo
isOrderedCommRingℝ .IsOrderedCommRing.·MonoR< =
  λ x y z 0<z → <ᵣ-·ᵣo x y (z , 0<z)
isOrderedCommRingℝ .IsOrderedCommRing.0<1 = decℚ<ᵣ?


ℝOrderedCommRing : OrderedCommRing ℓ-zero ℓ-zero
fst ℝOrderedCommRing = ℝ
OrderedCommRingStr.0r (snd ℝOrderedCommRing) = ℝCR.0r
OrderedCommRingStr.1r (snd ℝOrderedCommRing) = ℝCR.1r
OrderedCommRingStr._+_ (snd ℝOrderedCommRing) = _+ᵣ_
OrderedCommRingStr._·_ (snd ℝOrderedCommRing) = _·ᵣ_
OrderedCommRingStr.-_ (snd ℝOrderedCommRing) = -ᵣ_
OrderedCommRingStr._<_ (snd ℝOrderedCommRing) = _<ᵣ_
OrderedCommRingStr._≤_ (snd ℝOrderedCommRing) = _≤ᵣ_
OrderedCommRingStr.isOrderedCommRing (snd ℝOrderedCommRing) =
  isOrderedCommRingℝ
