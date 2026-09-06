module Cubical.HITs.CauchyReals.Circle.Homotopy.Equivalence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Int.Fast using (ℤ; isSetℤ)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group.MorphismProperties using (invGroupIso)
open import Cubical.HITs.CauchyReals.Circle.Winding
open import Cubical.HITs.CauchyReals.Circle.Homotopy.Base
open import Cubical.HITs.CauchyReals.Circle.Homotopy.Algebra
open import Cubical.HITs.CauchyReals.Circle.Homotopy.Quotient
open import Cubical.HITs.CauchyReals.Circle.Homotopy.Integers
open import Cubical.HITs.CauchyReals.Circle.Homotopy.Classification
open import Cubical.HITs.CauchyReals.Circle.Homotopy.NullHomotopy public using
  (nullWindingIsNull; zero-winding-contracts)

-- Winding classifies maps modulo jointly uniformly continuous homotopies.
-- The group operation on maps is pointwise circle addition.
circleHomotopy≅ℤ : AbGroupIso CircleHomotopyAbGroup IntegerAbGroup
circleHomotopy≅ℤ = classificationFromNullWinding nullWindingIsNull

ℤ≅circleHomotopy : AbGroupIso IntegerAbGroup CircleHomotopyAbGroup
ℤ≅circleHomotopy = invGroupIso circleHomotopy≅ℤ

circleHomotopy≃ℤ : CircleHomotopyClasses ≃ ℤ
circleHomotopy≃ℤ = isoToEquiv (fst circleHomotopy≅ℤ)

circleHomotopyAbGroupEquiv : AbGroupEquiv CircleHomotopyAbGroup IntegerAbGroup
circleHomotopyAbGroupEquiv = circleHomotopy≃ℤ , snd circleHomotopy≅ℤ

-- The inverse sends k to the class of the kth pointwise power of identity.
integerClass-winding : ∀ x → integerClass (classWinding x) ≡ x
integerClass-winding = Iso.ret (fst circleHomotopy≅ℤ)

winding-complete : (f g : CircleMap) →
  windingNumber f ≡ windingNumber g → Homotopic f g
winding-complete f g same = class-effective f g
  (nullWinding→injective nullWindingIsNull (class f) (class g) same)

winding-classifies : (f g : CircleMap) →
  Homotopic f g ≃ (windingNumber f ≡ windingNumber g)
winding-classifies f g = propBiimpl→Equiv squash₁ (isSetℤ _ _)
  (PT.rec (isSetℤ _ _) (windingNumber-homotopy f g)) (winding-complete f g)

winding-normal-form : (f : CircleMap) → Homotopic f (integerMap (windingNumber f))
winding-normal-form f = winding-complete f (integerMap (windingNumber f))
  (sym (winding-integerMap (windingNumber f)))
