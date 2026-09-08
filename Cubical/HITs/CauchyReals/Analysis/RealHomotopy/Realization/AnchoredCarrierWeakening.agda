module Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.AnchoredCarrierWeakening where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Pointed.Base using (Pointed; _→∙_)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.CubicalShapes
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.SelectedFaceCarriers
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.CarrierAnchors
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.PointedCarrierMaps

-- For a fixed inclusion, the whole common face parametrizes transitions.
-- Its homotopy anchor is supplied by anchorComparison, not chosen anew
-- as an arbitrary path in the sphere.
module AlongInclusion (n : ℕ) (s t : Selection n)
  (e : SelectionInclusion n s t) (inhabited : HasSelectedFace n s) where
  private
    target-inhabited = inclusion-inhabited n e inhabited

  sourcePoint : Anchor n t → Carrier n s
  sourcePoint = anchorCarrier n e inhabited

  targetPoint : Anchor n t → Carrier n t
  targetPoint = anchorCarrier n (selectionIdentity n t) target-inhabited

  source∙ target∙ boundary∙ : Anchor n t → Pointed ℓ-zero
  source∙ a = Carrier n s , sourcePoint a
  target∙ a = Carrier n t , targetPoint a
  boundary∙ a = CubeBoundary n , carrierBoundaryMap n t (targetPoint a)

  sourceBoundary : (a : Anchor n t) → source∙ a →∙ boundary∙ a
  sourceBoundary a = carrierBoundaryMap n s , anchorComparison n e inhabited a

  targetBoundary : (a : Anchor n t) → target∙ a →∙ boundary∙ a
  targetBoundary a = carrierBoundaryMap n t , refl

  TransitionAt : Anchor n t → Type
  TransitionAt a = PointedOver (sourceBoundary a) (targetBoundary a)

  transitionAt-contractible : (a : Anchor n t) → isContr (TransitionAt a)
  transitionAt-contractible a = pointed-over-contractible (sourceBoundary a) (targetBoundary a)
    (carrier-contractible n s inhabited)

  transitionAt : (a : Anchor n t) → TransitionAt a
  transitionAt a = fst (transitionAt-contractible a)

  -- The full unpointed over-map type is constant as the anchor moves.
  -- It retains the sphere-valued commuting homotopy.
  OverBoundary : Type
  OverBoundary = Σ[ w ∈ (Carrier n s → Carrier n t) ]
    (λ x → carrierBoundaryMap n t (w x)) ≡ carrierBoundaryMap n s

  transitionOver : Anchor n t → OverBoundary
  transitionOver a =
    overMap {p = sourceBoundary a} {q = targetBoundary a} (transitionAt a) ,
    overMap-commutes {p = sourceBoundary a} {q = targetBoundary a} (transitionAt a)

  anchor-independent : (a b : Anchor n t) → transitionOver a ≡ transitionOver b
  anchor-independent a b = cong transitionOver (isContr→isProp (anchor-contractible n t) a b)

  weakeningOver : OverBoundary
  weakeningOver = transitionOver (fst (anchor-contractible n t))

  weakeningOver-at : (a : Anchor n t) → weakeningOver ≡ transitionOver a
  weakeningOver-at a = cong transitionOver (snd (anchor-contractible n t) a)

-- This proves anchor independence for ONE fixed inclusion with the
-- displayed normalization. It does not compare different inclusions or
-- prove the direct/composite law for a chain s ⊆ t ⊆ u.
