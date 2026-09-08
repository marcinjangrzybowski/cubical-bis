module Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.CarrierAnchors where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Bool using (Bool)
open import Cubical.Data.Unit using (Unit; tt; isContrUnit)
open import Cubical.Data.Empty using (rec)
open import Cubical.Data.Sigma
open import Cubical.HITs.Interval.Base using ()
  renaming (Interval to 𝕁; isContrInterval to isContr𝕁)
open import Cubical.HITs.Pushout.Base
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.SquareBoundary
  using (endpoints)
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.CubicalShapes
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.SelectedFaceCarriers

-- Inclusions never change the sign of an already selected face.
data FaceInclusion : FaceSelection → FaceSelection → Type where
  fromOmit : (a : FaceSelection) → FaceInclusion omit a
  sameFace : (b : Bool) → FaceInclusion (choose b) (choose b)

SelectionInclusion : (n : ℕ) → Selection n → Selection n → Type
SelectionInclusion zero s t = Unit
SelectionInclusion (suc n) (a , s) (b , t) = FaceInclusion a b × SelectionInclusion n s t

selectionIdentity : (n : ℕ) (s : Selection n) → SelectionInclusion n s s
selectionIdentity zero s = tt
selectionIdentity (suc n) (omit , s) = fromOmit omit , selectionIdentity n s
selectionIdentity (suc n) (choose b , s) = sameFace b , selectionIdentity n s

inclusion-inhabited : (n : ℕ) {s t : Selection n} →
  SelectionInclusion n s t → HasSelectedFace n s → HasSelectedFace n t
inclusion-inhabited zero e = rec
inclusion-inhabited (suc n) {s = omit , s} {t = omit , t} (fromOmit omit , e) h =
  inclusion-inhabited n e h
inclusion-inhabited (suc n) {s = omit , s} {t = choose b , t} (fromOmit (choose b) , e) h = tt
inclusion-inhabited (suc n) {s = choose b , s} {t = choose .b , t} (sameFace .b , e) h = tt

-- Intersection of the chosen faces: selected coordinates are fixed,
-- and unselected coordinates vary over the synthetic interval.
AnchorAxis : FaceSelection → Type
AnchorAxis omit = 𝕁
AnchorAxis (choose b) = Unit

anchorCoordinate : (a : FaceSelection) → AnchorAxis a → 𝕁
anchorCoordinate omit x = x
anchorCoordinate (choose b) _ = endpoints b

Anchor : (n : ℕ) → Selection n → Type
Anchor zero s = Unit
Anchor (suc n) (a , s) = AnchorAxis a × Anchor n s

anchor-contractible : (n : ℕ) (s : Selection n) → isContr (Anchor n s)
anchor-contractible zero s = isContrUnit
anchor-contractible (suc n) (omit , s) = isContrΣ isContr𝕁 (λ _ → anchor-contractible n s)
anchor-contractible (suc n) (choose b , s) = isContrΣ isContrUnit (λ _ → anchor-contractible n s)

anchorDisk : (n : ℕ) (s : Selection n) → Anchor n s → CubeDisk n
anchorDisk zero s x = tt
anchorDisk (suc n) (a , s) (x , xs) = anchorCoordinate a x , anchorDisk n s xs

anchorCarrier : (n : ℕ) {s t : Selection n} → SelectionInclusion n s t →
  HasSelectedFace n s → Anchor n t → Carrier n s
anchorCarrier zero e = rec
anchorCarrier (suc n) {s = omit , s} {t = a , t} (fromOmit a , e) h (x , xs) =
  inr (anchorCoordinate a x , anchorCarrier n e h xs)
anchorCarrier (suc n) {s = choose b , s} {t = choose .b , t} (sameFace .b , e) h (x , xs) =
  inl (tt , anchorDisk n t xs)

anchorCarrier-disk : (n : ℕ) {s t : Selection n}
  (e : SelectionInclusion n s t) (h : HasSelectedFace n s) (x : Anchor n t) →
  carrierDiskMap n s (anchorCarrier n e h x) ≡ anchorDisk n t x
anchorCarrier-disk zero e () x
anchorCarrier-disk (suc n) {s = omit , s} {t = a , t} (fromOmit a , e) h (x , xs) =
  cong (anchorCoordinate a x ,_) (anchorCarrier-disk n e h xs)
anchorCarrier-disk (suc n) {s = choose b , s} {t = choose .b , t} (sameFace .b , e) h (x , xs) = refl

-- A WHOLE parameterized boundary homotopy for s ⊆ t. In the only
-- nontrivial constructor case the actual boundary push path moves from
-- a side face to the newly selected first face; disk contractibility
-- supplies only the adjustment WITHIN that first face.
anchorComparison : (n : ℕ) {s t : Selection n}
  (e : SelectionInclusion n s t) (h : HasSelectedFace n s) (x : Anchor n t) →
  carrierBoundaryMap n s (anchorCarrier n e h x) ≡
  carrierBoundaryMap n t
    (anchorCarrier n (selectionIdentity n t) (inclusion-inhabited n e h) x)
anchorComparison zero e () x
anchorComparison (suc n) {s = choose b , s} {t = choose .b , t} (sameFace .b , e) h (x , xs) = refl
anchorComparison (suc n) {s = omit , s} {t = omit , t} (fromOmit omit , e) h (x , xs) =
  cong {B = λ _ → CubeBoundary (suc n)} (λ z → inr (x , z)) (anchorComparison n e h xs)
anchorComparison (suc n) {s = omit , s} {t = choose b , t}
  (fromOmit (choose b) , e) h (x , xs) =
  sym (push (b , carrierBoundaryMap n s (anchorCarrier n e h xs))) ∙
  cong {B = λ _ → CubeBoundary (suc n)} (λ d → inl (b , d))
    (isContr→isProp (isContrCubeDisk n) _ (anchorDisk n t xs))

-- Comparing its endpoint values with the existing pointed corner
-- structures also requires their normalization squares. No independence
-- of arbitrary routes through different carriers is asserted here.
