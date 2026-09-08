module Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.CarrierCornerNormalization where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function using (homotopyNatural)
open import Cubical.Foundations.GroupoidLaws using (lUnit; rUnit; assoc; cong-∙)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Bool using (Bool)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty using (rec)
open import Cubical.Data.Sigma
open import Cubical.HITs.Pushout.Base
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.SquareBoundary
  using (endpoints)
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.CubicalShapes
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.SelectedFaceCarriers
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.CarrierCorners
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.CarrierAnchors

-- Boolean corners of the whole common coordinate face. Selected
-- coordinates already have their sign; only omitted coordinates vary.
DiscreteAxis : FaceSelection → Type
DiscreteAxis omit = Bool
DiscreteAxis (choose b) = Unit

discreteLabel : (a : FaceSelection) → DiscreteAxis a → Bool
discreteLabel omit b = b
discreteLabel (choose b) _ = b

axisAnchor : (a : FaceSelection) → DiscreteAxis a → AnchorAxis a
axisAnchor omit b = endpoints b
axisAnchor (choose b) _ = tt

DiscreteAnchor : (n : ℕ) → Selection n → Type
DiscreteAnchor zero s = Unit
DiscreteAnchor (suc n) (a , s) = DiscreteAxis a × DiscreteAnchor n s

discreteCorner : (n : ℕ) (s : Selection n) → DiscreteAnchor n s → Corner n
discreteCorner zero s x = tt
discreteCorner (suc n) (a , s) (x , xs) = discreteLabel a x , discreteCorner n s xs

discreteAnchor : (n : ℕ) (s : Selection n) → DiscreteAnchor n s → Anchor n s
discreteAnchor zero s x = tt
discreteAnchor (suc n) (a , s) (x , xs) = axisAnchor a x , discreteAnchor n s xs

axis-normalization : (a : FaceSelection) (x : DiscreteAxis a) →
  anchorCoordinate a (axisAnchor a x) ≡ endpoints (discreteLabel a x)
axis-normalization omit x = refl
axis-normalization (choose b) x = refl

disk-normalization : (n : ℕ) (t : Selection n) (v : DiscreteAnchor n t) →
  anchorDisk n t (discreteAnchor n t v) ≡ diskCorner n (discreteCorner n t v)
disk-normalization zero t v = refl
disk-normalization (suc n) (a , t) (x , xs) =
  ΣPathP (axis-normalization a x , disk-normalization n t xs)

inclusion-compatible : (n : ℕ) {s t : Selection n}
  (e : SelectionInclusion n s t) (v : DiscreteAnchor n t) →
  CompatibleCorner n s (discreteCorner n t v)
inclusion-compatible zero e v = tt
inclusion-compatible (suc n) {s = omit , s} {t = a , t} (fromOmit a , e) (x , xs) =
  (λ ()) , inclusion-compatible n e xs
inclusion-compatible (suc n) {s = choose b , s} {t = choose .b , t} (sameFace .b , e) (x , xs) =
  (λ _ → refl) , inclusion-compatible n e xs

-- These endpoint paths are retained by the boundary normalization law;
-- they cannot be discarded just because the carrier is contractible.
corner-normalization : (n : ℕ) {s t : Selection n}
  (e : SelectionInclusion n s t) (h : HasSelectedFace n s) (v : DiscreteAnchor n t) →
  anchorCarrier n e h (discreteAnchor n t v) ≡
  carrierCorner n s h (discreteCorner n t v)
corner-normalization zero e () v
corner-normalization (suc n) {s = omit , s} {t = a , t} (fromOmit a , e) h (x , xs) =
  cong inr (ΣPathP (axis-normalization a x , corner-normalization n e h xs))
corner-normalization (suc n) {s = choose b , s} {t = choose .b , t} (sameFace .b , e) h (x , xs) =
  cong (λ d → inl (tt , d)) (disk-normalization n t xs)

module Endpoint (n : ℕ) {s t : Selection (suc n)}
  (e : SelectionInclusion (suc n) s t) (h : HasSelectedFace (suc n) s)
  (v : DiscreteAnchor (suc n) t) where

  endpointBoundary :
    carrierBoundaryMap (suc n) s (anchorCarrier (suc n) e h (discreteAnchor (suc n) t v)) ≡
    boundaryCorner n (discreteCorner (suc n) t v)
  endpointBoundary =
    cong (carrierBoundaryMap (suc n) s) (corner-normalization (suc n) e h v) ∙
    carrierCorner-boundary n s h (discreteCorner (suc n) t v)
      (inclusion-compatible (suc n) e v)

open Endpoint using (endpointBoundary)

private
  selected-endpoint : (n : ℕ) {s t : Selection n} (b : Bool)
    (e : SelectionInclusion n s t) (h : Unit) (v : DiscreteAnchor n t) →
    endpointBoundary n {s = choose b , s} {t = choose b , t}
      (sameFace b , e) h (tt , v) ≡
    cong (λ d → inl (b , d)) (disk-normalization n t v)
  selected-endpoint n b e h v = sym (rUnit _)

  omitted-at-omitted : (n : ℕ) {s t : Selection (suc n)} (x : Bool)
    (e : SelectionInclusion (suc n) s t) (h : HasSelectedFace (suc n) s)
    (v : DiscreteAnchor (suc n) t) →
    endpointBoundary (suc n) {s = omit , s} {t = omit , t}
      (fromOmit omit , e) h (x , v) ≡
    cong {B = λ _ → CubeBoundary (suc (suc n))}
      (λ z → inr (endpoints x , z)) (endpointBoundary n e h v) ∙
    sym (push (x , boundaryCorner n (discreteCorner (suc n) t v)))
  omitted-at-omitted n {s = s} {t = t} x e h v =
    assoc _ _ H ∙ cong (_∙ H) (sym (cong-∙ R
      (cong (carrierBoundaryMap (suc n) s) (corner-normalization (suc n) e h v))
      (carrierCorner-boundary n s h (discreteCorner (suc n) t v)
        (inclusion-compatible (suc n) e v))))
    where
    R : CubeBoundary (suc n) → CubeBoundary (suc (suc n))
    R z = inr (endpoints x , z)
    H = sym (push (x , boundaryCorner n (discreteCorner (suc n) t v)))

  omitted-at-selected : (n : ℕ) {s t : Selection (suc n)} (b : Bool)
    (e : SelectionInclusion (suc n) s t) (h : HasSelectedFace (suc n) s)
    (v : DiscreteAnchor (suc n) t) →
    endpointBoundary (suc n) {s = omit , s} {t = choose b , t}
      (fromOmit (choose b) , e) h (tt , v) ≡
    cong {B = λ _ → CubeBoundary (suc (suc n))}
      (λ z → inr (endpoints b , z)) (endpointBoundary n e h v) ∙
    sym (push (b , boundaryCorner n (discreteCorner (suc n) t v)))
  omitted-at-selected n {s = s} {t = t} b e h v =
    assoc _ _ H ∙ cong (_∙ H) (sym (cong-∙ R
      (cong (carrierBoundaryMap (suc n) s) (corner-normalization (suc n) e h v))
      (carrierCorner-boundary n s h (discreteCorner (suc n) t v)
        (inclusion-compatible (suc n) e v))))
    where
    R : CubeBoundary (suc n) → CubeBoundary (suc (suc n))
    R z = inr (endpoints b , z)
    H = sym (push (b , boundaryCorner n (discreteCorner (suc n) t v)))

-- The complete normalization square at a generated common corner.
-- Both sides retain their endpoint normalization paths in the sphere.
endpoint-normalization : (n : ℕ) {s t : Selection (suc n)}
  (e : SelectionInclusion (suc n) s t) (h : HasSelectedFace (suc n) s)
  (v : DiscreteAnchor (suc n) t) →
  anchorComparison (suc n) e h (discreteAnchor (suc n) t v) ∙
    endpointBoundary n (selectionIdentity (suc n) t) (inclusion-inhabited (suc n) e h) v ≡
  endpointBoundary n e h v
endpoint-normalization n {s = choose b , s} {t = choose .b , t}
  (sameFace .b , e) h (x , v) = sym (lUnit _)
endpoint-normalization zero {s = omit , s} e () v
endpoint-normalization (suc n) {s = omit , s} {t = omit , t}
  (fromOmit omit , e) h (x , v) =
  cong (cong R E ∙_) (omitted-at-omitted n x
    (selectionIdentity (suc n) t) (inclusion-inhabited (suc n) e h) v) ∙
  assoc (cong R E) (cong R pt) H ∙
  cong (_∙ H) (sym (cong-∙ R E pt)) ∙
  cong (λ p → cong R p ∙ H) (endpoint-normalization n e h v) ∙
  sym (omitted-at-omitted n x e h v)
  where
  R : CubeBoundary (suc n) → CubeBoundary (suc (suc n))
  R z = inr (endpoints x , z)
  E = anchorComparison (suc n) e h (discreteAnchor (suc n) t v)
  pt = endpointBoundary n (selectionIdentity (suc n) t) (inclusion-inhabited (suc n) e h) v
  H = sym (push (x , boundaryCorner n (discreteCorner (suc n) t v)))
endpoint-normalization (suc n) {s = omit , s} {t = choose b , t}
  (fromOmit (choose b) , e) h (x , v) =
  cong ((H z ∙ cong L ε) ∙_) (selected-endpoint (suc n) b
    (selectionIdentity (suc n) t) tt v) ∙
  sym (assoc (H z) (cong L ε) (cong L δ)) ∙
  cong (H z ∙_) (sym (cong-∙ L ε δ)) ∙
  cong (λ d → H z ∙ cong L d)
    (isProp→isSet (isContr→isProp (isContrCubeDisk (suc n))) _ _
      (ε ∙ δ) (cong (cubeBoundaryMap (suc n)) p)) ∙
  homotopyNatural H p ∙
  sym (omitted-at-selected n b e h v)
  where
  L : CubeDisk (suc n) → CubeBoundary (suc (suc n))
  L d = inl (b , d)
  z = carrierBoundaryMap (suc n) s (anchorCarrier (suc n) e h (discreteAnchor (suc n) t v))
  H : (z : CubeBoundary (suc n)) → inr (endpoints b , z) ≡ L (cubeBoundaryMap (suc n) z)
  H z = sym (push (b , z))
  ε = isContr→isProp (isContrCubeDisk (suc n))
    (cubeBoundaryMap (suc n) z) (anchorDisk (suc n) t (discreteAnchor (suc n) t v))
  δ = disk-normalization (suc n) t v
  p = endpointBoundary n e h v
