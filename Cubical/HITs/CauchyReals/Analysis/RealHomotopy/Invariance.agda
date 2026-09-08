module Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Invariance where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Transport
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties using (idGroupIso)
open import Cubical.Relation.Premetric.Mappings
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Groups

PointedIsometry : ∀ {ℓ ℓ'} →
  PointedPremetricSpace ℓ ℓ' → PointedPremetricSpace ℓ ℓ' → Type _
PointedIsometry (X , x) (Y , y) =
  Σ[ e ∈ PremetricSpaceEquiv X Y ] equivFun (fst e) x ≡ y

pointedIsometryPath : ∀ {ℓ ℓ'} {X Y : PointedPremetricSpace ℓ ℓ'} →
  PointedIsometry X Y → X ≡ Y
pointedIsometryPath {X = X , x} {Y = Y , y} (e , based) =
  ΣPathP (equivFun (PremetricSIP X Y) e , toPathP (uaβ (fst e) x ∙ based))

-- Isometries preserve every degree, including the group operation.
opaque
  realπ-isometry : ∀ {ℓ ℓ'} (n : ℕ) {X Y : PointedPremetricSpace ℓ ℓ'} →
    PointedIsometry X Y → GroupIso (realπGr n X) (realπGr n Y)
  realπ-isometry n {X = X} {Y = Y} e = subst (λ Z → GroupIso (realπGr n X) (realπGr n Z))
    (pointedIsometryPath {X = X} {Y = Y} e) (idGroupIso {G = realπGr n X})
