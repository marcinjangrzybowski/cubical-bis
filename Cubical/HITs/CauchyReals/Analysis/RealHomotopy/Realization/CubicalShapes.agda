module Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.CubicalShapes where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Bool using (Bool)
open import Cubical.Data.Empty using (⊥; rec)
open import Cubical.Data.Unit using (Unit; tt; isContrUnit)
open import Cubical.Data.Sigma
open import Cubical.HITs.Interval.Base using ()
  renaming (Interval to 𝕁; isContrInterval to isContr𝕁)
open import Cubical.HITs.Pushout.Base
open import Cubical.HITs.Pushout.Properties using (pushoutIso)
open import Cubical.HITs.Pushout.PushoutProduct using (PushProd; _×̂_)
open import Cubical.HITs.Join.Base using (join)
open import Cubical.HITs.Join.Properties using (joinPushout-iso-join; join-comm)
open import Cubical.HITs.Susp.Base
open import Cubical.HITs.Susp.Properties using (Susp-iso-joinBool)
open import Cubical.HITs.Sn.Base using (S₊)
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.SquareBoundary
  using (endpoints)

-- These are synthetic shapes, not a realization of singular data.
-- One recursive definition includes every corner and face intersection.
CubeDisk : ℕ → Type
CubeDisk zero = Unit
CubeDisk (suc n) = 𝕁 × CubeDisk n

CubeBoundary : ℕ → Type
cubeBoundaryMap : (n : ℕ) → CubeBoundary n → CubeDisk n
CubeBoundary zero = ⊥
CubeBoundary (suc n) = PushProd endpoints (cubeBoundaryMap n)
cubeBoundaryMap zero = rec
cubeBoundaryMap (suc n) = endpoints ×̂ cubeBoundaryMap n

isContrCubeDisk : (n : ℕ) → isContr (CubeDisk n)
isContrCubeDisk zero = isContrUnit
isContrCubeDisk (suc n) = isContrΣ isContr𝕁 (λ _ → isContrCubeDisk n)

private
  fstIso : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → isContr B → Iso (A × B) A
  Iso.fun (fstIso c) = fst
  Iso.inv (fstIso c) a = a , fst c
  Iso.sec (fstIso c) a = refl
  Iso.ret (fstIso c) (a , b) i = a , snd c b i

  sndIso : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → isContr A → Iso (A × B) B
  Iso.fun (sndIso c) = snd
  Iso.inv (sndIso c) b = fst c , b
  Iso.sec (sndIso c) b = refl
  Iso.ret (sndIso c) (a , b) i = snd c a i , b

-- The boundary of a product of contractible disks is the join of their
-- boundaries. Only the disks are contracted, not the boundary types.
pushoutProductJoinIso : ∀ {ℓA ℓB ℓC ℓD}
  {A : Type ℓA} {B : Type ℓB} {C : Type ℓC} {D : Type ℓD}
  (f : A → C) (g : B → D) → isContr C → isContr D →
  Iso (PushProd f g) (join A B)
pushoutProductJoinIso {A = A} {B = B} f g cC cD =
  compIso
    (pushoutIso (λ (a , b) → a , g b) (λ (a , b) → f a , b)
      fst snd (idEquiv (A × B)) (isoToEquiv (fstIso cD)) (isoToEquiv (sndIso cC))
      refl refl)
    (joinPushout-iso-join A B)

boundarySuccessorIso : (n : ℕ) → Iso (CubeBoundary (suc n)) (Susp (CubeBoundary n))
boundarySuccessorIso n = compIso
  (pushoutProductJoinIso endpoints (cubeBoundaryMap n) isContr𝕁 (isContrCubeDisk n))
  (compIso join-comm (invIso Susp-iso-joinBool))

private
  suspSphereIso : (n : ℕ) → Iso (Susp (S₊ n)) (S₊ (suc n))
  suspSphereIso zero = invIso S¹IsoSuspBool
  suspSphereIso (suc n) = idIso

-- A single induction, for all dimensions, identifies the cubical
-- boundary with the library's synthetic sphere.
cubeBoundarySphereIso : (n : ℕ) → Iso (CubeBoundary (suc n)) (S₊ n)
cubeBoundarySphereIso zero = compIso (boundarySuccessorIso zero) (invIso BoolIsoSusp⊥)
cubeBoundarySphereIso (suc n) = compIso (boundarySuccessorIso (suc n))
  (compIso (IsoType→IsoSusp (cubeBoundarySphereIso n)) (suspSphereIso n))

cubeBoundarySphereEquiv : (n : ℕ) → CubeBoundary (suc n) ≃ S₊ n
cubeBoundarySphereEquiv n = isoToEquiv (cubeBoundarySphereIso n)

-- Collapsing the whole boundary of an (n+1)-disk gives an (n+1)-sphere.
-- The quotient here is the untruncated homotopy cofiber.
private
  cofiberSuspIso : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
    (f : A → B) → isContr B → Iso (cofib f) (Susp A)
  cofiberSuspIso {A = A} f cB = compIso
    (pushoutIso (λ _ → tt) f (λ _ → tt) (λ _ → tt)
      (idEquiv A) (idEquiv Unit) (isoToEquiv (isContr→Iso cB isContrUnit)) refl refl)
    PushoutSuspIsoSusp

cubeCofiberSphereIso : (n : ℕ) → Iso (cofib (cubeBoundaryMap (suc n))) (S₊ (suc n))
cubeCofiberSphereIso n = compIso
  (cofiberSuspIso (cubeBoundaryMap (suc n)) (isContrCubeDisk (suc n)))
  (compIso (IsoType→IsoSusp (cubeBoundarySphereIso n)) (suspSphereIso n))
