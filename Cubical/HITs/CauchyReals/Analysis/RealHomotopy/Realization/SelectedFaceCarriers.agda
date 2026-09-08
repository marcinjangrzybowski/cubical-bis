module Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.SelectedFaceCarriers where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Bool using (Bool)
open import Cubical.Data.Empty using (⊥; rec)
open import Cubical.Data.Unit using (Unit; tt; isContrUnit)
open import Cubical.Data.Sigma
open import Cubical.HITs.Interval.Base using ()
  renaming (Interval to 𝕁; isContrInterval to isContr𝕁)
open import Cubical.HITs.Pushout.Base
open import Cubical.HITs.Pushout.PushoutProduct using (PushProd; _×̂_)
open import Cubical.HITs.Join.Properties using (isContrJoinL; isContrJoinR)
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.SquareBoundary
  using (endpoints)
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.CubicalShapes

-- At most one signed face per coordinate: selected faces have a common
-- corner. Their UNION, including intersections, is represented by a HIT.
data FaceSelection : Type where
  omit : FaceSelection
  choose : Bool → FaceSelection

Endpoint : FaceSelection → Type
Endpoint omit = ⊥
Endpoint (choose b) = Unit

endpointLabel : (a : FaceSelection) → Endpoint a → Bool
endpointLabel omit = rec
endpointLabel (choose b) _ = b

selectedEndpoint : (a : FaceSelection) → Endpoint a → 𝕁
selectedEndpoint a x = endpoints (endpointLabel a x)

Selection : ℕ → Type
Selection zero = Unit
Selection (suc n) = FaceSelection × Selection n

HasSelectedFace : (n : ℕ) → Selection n → Type
HasSelectedFace zero _ = ⊥
HasSelectedFace (suc n) (omit , s) = HasSelectedFace n s
HasSelectedFace (suc n) (choose b , s) = Unit

Carrier : (n : ℕ) → Selection n → Type
carrierDiskMap : (n : ℕ) (s : Selection n) → Carrier n s → CubeDisk n
Carrier zero _ = ⊥
Carrier (suc n) (a , s) = PushProd (selectedEndpoint a) (carrierDiskMap n s)
carrierDiskMap zero _ = rec
carrierDiskMap (suc n) (a , s) = selectedEndpoint a ×̂ carrierDiskMap n s

carrier-contractible : (n : ℕ) (s : Selection n) →
  HasSelectedFace n s → isContr (Carrier n s)
carrier-contractible zero s = rec
carrier-contractible (suc n) (omit , s) inhabited =
  isOfHLevelRetractFromIso 0
    (pushoutProductJoinIso (selectedEndpoint omit) (carrierDiskMap n s)
      isContr𝕁 (isContrCubeDisk n))
    (isContrJoinR (carrier-contractible n s inhabited))
carrier-contractible (suc n) (choose b , s) _ =
  isOfHLevelRetractFromIso 0
    (pushoutProductJoinIso (selectedEndpoint (choose b)) (carrierDiskMap n s)
      isContr𝕁 (isContrCubeDisk n))
    (isContrJoinL isContrUnit)

-- One recursion gives actual maps into the synthetic cubical boundary.
-- The commuting path lives in the contractible DISK, so it can be
-- obtained uniformly without assuming contractibility of the sphere.
carrierBoundaryMap : (n : ℕ) (s : Selection n) → Carrier n s → CubeBoundary n
carrier-in-disk : (n : ℕ) (s : Selection n) (c : Carrier n s) →
  cubeBoundaryMap n (carrierBoundaryMap n s c) ≡ carrierDiskMap n s c
carrierBoundaryMap zero s = rec
carrierBoundaryMap (suc n) (a , s) (inl (e , d)) = inl (endpointLabel a e , d)
carrierBoundaryMap (suc n) (a , s) (inr (t , c)) = inr (t , carrierBoundaryMap n s c)
carrierBoundaryMap (suc n) (a , s) (push (e , c) i) =
  (cong {B = λ _ → CubeBoundary (suc n)} (λ d → inl (endpointLabel a e , d))
    (sym (carrier-in-disk n s c)) ∙
    push (endpointLabel a e , carrierBoundaryMap n s c)) i
carrier-in-disk n s c = isContr→isProp (isContrCubeDisk n) _ _

-- No carrier-inclusion/weakening theorem for complete carried grid maps
-- is asserted here. These canonical shapes and maps are its inputs.
