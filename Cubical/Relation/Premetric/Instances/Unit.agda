module Cubical.Relation.Premetric.Instances.Unit where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Data.Unit

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveHalvesℚ

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings


private
  variable
    ℓ ℓ' : Level


UnitPremetricStr : PremetricStr ℓ-zero Unit
PremetricStr._≈[_]_ UnitPremetricStr _ _ _ = Unit
PremetricStr.isPremetric UnitPremetricStr = unitIsPremetric
  where
  open IsPremetric

  unitIsPremetric : IsPremetric (PremetricStr._≈[_]_ UnitPremetricStr)
  unitIsPremetric .isSetM = isProp→isSet isPropUnit
  unitIsPremetric .isProp≈ _ _ _ = isPropUnit
  unitIsPremetric .isRefl≈ _ _ = tt
  unitIsPremetric .isSym≈ _ _ _ _ = tt
  unitIsPremetric .isSeparated≈ x y _ = isPropUnit x y
  unitIsPremetric .isTriangular≈ _ _ _ _ _ _ _ = tt
  unitIsPremetric .isRounded≈ _ _ ε _ =
    ∣ ε /2₊ , /2₊<id ε , tt ∣₁


UnitPremetricSpace : PremetricSpace ℓ-zero ℓ-zero
UnitPremetricSpace = Unit , UnitPremetricStr


fromUnitNE :
  (N : PremetricSpace ℓ ℓ') →
  (f : Unit → ⟨ N ⟩) →
  NE[ UnitPremetricSpace , N ]
fst (fromUnitNE N f) = f
IsNonExpanding.pres≈ (snd (fromUnitNE N f)) tt tt ε _ =
  PremetricStr.isRefl≈ (snd N) (f tt) ε


fromUnitUC :
  (N : PremetricSpace ℓ ℓ') →
  (f : Unit → ⟨ N ⟩) →
  UC[ UnitPremetricSpace , N ]
fromUnitUC N f = NE→UC (fromUnitNE N f)
