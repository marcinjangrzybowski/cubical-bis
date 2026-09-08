module Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.CarriedMaps where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv.Base using (fiber)
open import Cubical.Foundations.GroupoidLaws using (lUnit; assoc; cong-∙)
open import Cubical.Foundations.Pointed.Base using (Pointed; _→∙_)
open import Cubical.Foundations.Pointed.Properties using (_∘∙_; ∘∙-assoc)
open import Cubical.Data.Sigma
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.PointedCarrierMaps

private
  variable
    ℓB ℓC ℓD ℓS ℓP ℓQ ℓR : Level
    B : Type ℓB
    C : Type ℓC
    D : Type ℓD
    S : Type ℓS

-- Membership in a carrier is a full homotopy fiber, not a proposition.
CarriedMap : (C → S) → (D → S) → Type _
CarriedMap e f = (x : _) → fiber e (f x)

restrictCarried : {e : C → S} {f : D → S} (i : B → D) →
  CarriedMap e f → CarriedMap e (λ z → f (i z))
restrictCarried i c z = c (i z)

module _ {ℓC'} {C' : Type ℓC'} (e : C → S) (e' : C' → S)
  (W : (s : S) → fiber e s → fiber e' s) where

  mapCarried : (f : D → S) → CarriedMap e f → CarriedMap e' f
  mapCarried f c x = W (f x) (c x)

  map-restrict : (f : D → S) (i : B → D) (c : CarriedMap e f) →
    restrictCarried {e = e'} {f = f} i (mapCarried f c) ≡
    mapCarried (λ z → f (i z)) (restrictCarried {e = e} {f = f} i c)
  map-restrict f i c = refl

-- This includes the boundary agreement as data and works for arbitrary
-- domain/boundary shapes. It transports supplied extensions; it does not
-- assert that a fixed sphere-valued map has a carrier lift.
RelativeSections : (i : B → D) (P : D → Type ℓP) →
  ((z : B) → P (i z)) → Type _
RelativeSections i P b = Σ[ g ∈ ((x : _) → P x) ] (λ z → g (i z)) ≡ b

mapRelativeSections : (i : B → D) (P : D → Type ℓP) (Q : D → Type ℓQ)
  (W : (x : D) → P x → Q x) (b : (z : B) → P (i z)) →
  RelativeSections i P b → RelativeSections i Q (λ z → W (i z) (b z))
mapRelativeSections i P Q W b (g , p) = (λ x → W x (g x)) ,
  cong (λ q z → W (i z) (q z)) p

private
  variable
    ℓX ℓY ℓZ ℓT : Level
    X : Pointed ℓX
    Y : Pointed ℓY
    Z : Pointed ℓZ
    T : Pointed ℓT

-- Turn a complete pointed transition into a fiberwise operation.
fiberAction : {p : X →∙ T} {q : Y →∙ T} → PointedOver p q →
  (s : fst T) → fiber (fst p) s → fiber (fst q) s
fiberAction {p = p} {q = q} w s (x , α) =
  overMap {p = p} {q = q} w x ,
  funExt⁻ (overMap-commutes {p = p} {q = q} w) x ∙ α

fiberAction-identity : (p : X →∙ T) (s : fst T) (z : fiber (fst p) s) →
  fiberAction {p = p} {q = p} (identityOver p) s z ≡ z
fiberAction-identity p s (x , α) = ΣPathP (refl , sym (lUnit α))

private
  commutes-compose : {p : X →∙ T} {q : Y →∙ T} {r : Z →∙ T}
    (g : PointedOver q r) (f : PointedOver p q) (x : fst X) →
    funExt⁻ (overMap-commutes {p = p} {q = r}
      (composeOver {p = p} {q = q} {r = r} g f)) x ≡
    funExt⁻ (overMap-commutes {p = q} {q = r} g) (overMap {p = p} {q = q} f x) ∙
    funExt⁻ (overMap-commutes {p = p} {q = q} f) x
  commutes-compose {r = r} (g , β) (f , α) x =
    cong-∙ (λ k → fst k x) (sym (∘∙-assoc r g f)) (cong (λ k → k ∘∙ f) β ∙ α) ∙
    sym (lUnit (cong (λ k → fst k x) (cong (λ k → k ∘∙ f) β ∙ α))) ∙
    cong-∙ (λ k → fst k x) (cong (λ k → k ∘∙ f) β) α

fiberAction-composition : {p : X →∙ T} {q : Y →∙ T} {r : Z →∙ T}
  (g : PointedOver q r) (f : PointedOver p q) (s : fst T) (z : fiber (fst p) s) →
  fiberAction {p = p} {q = r} (composeOver {p = p} {q = q} {r = r} g f) s z ≡
  fiberAction {p = q} {q = r} g s (fiberAction {p = p} {q = q} f s z)
fiberAction-composition {p = p} {q = q} {r = r} g f s (x , α) = ΣPathP
  (refl , (cong (_∙ α) (commutes-compose {p = p} {q = q} {r = r} g f x) ∙
    sym (assoc
      (funExt⁻ (overMap-commutes {p = q} {q = r} g) (overMap {p = p} {q = q} f x))
      (funExt⁻ (overMap-commutes {p = p} {q = q} f) x) α)))
