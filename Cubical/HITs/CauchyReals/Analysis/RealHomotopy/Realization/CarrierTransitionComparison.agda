module Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.CarrierTransitionComparison where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path using (compPath→Square; isProp→isContrPathP)
open import Cubical.Foundations.GroupoidLaws using (lUnit)
open import Cubical.Foundations.Pointed.Base using (Pointed; _→∙_)
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Sigma
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.CubicalShapes
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.SelectedFaceCarriers
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.CarrierCorners
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.CarrierAnchors
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.PointedCarrierMaps
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.CornerWeakening
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.AnchoredCarrierWeakening
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.CarrierCornerNormalization
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.CarrierNormalizationFamilies

-- Compare the ACTUAL transitions, including their unpointed commuting
-- homotopies. The normalization supplies a path of entire pointed
-- presentations; contractibility is used within that specified path.
module Compare (n : ℕ) {s t : Selection (suc n)}
  (e : SelectionInclusion (suc n) s t) (h : HasSelectedFace (suc n) s)
  (v : DiscreteAnchor (suc n) t) where

  module A = AlongInclusion (suc n) s t e h
  module N = Normalize n e h v
  module C = AtCorner n (discreteCorner (suc n) t v)

  private
    ht = inclusion-inhabited (suc n) e h
    idt = selectionIdentity (suc n) t
    qs = carrierBoundaryMap (suc n) s
    qt = carrierBoundaryMap (suc n) t

  sourceCorner targetCorner : C.CornerCarrier
  sourceCorner = s , h , inclusion-compatible (suc n) e v
  targetCorner = t , ht , inclusion-compatible (suc n) idt v

  cornerTransition : A.OverBoundary
  cornerTransition =
    overMap {p = C.toBoundary sourceCorner} {q = C.toBoundary targetCorner}
      (C.transition sourceCorner targetCorner) ,
    overMap-commutes {p = C.toBoundary sourceCorner} {q = C.toBoundary targetCorner}
      (C.transition sourceCorner targetCorner)

  module AtAnchor (a : Anchor (suc n) t) where
    private
      κs = fst (N.normalization a)
      κt = fst (snd (N.normalization a))
      square = snd (snd (N.normalization a))
      βs = snd (C.toBoundary sourceCorner)
      βt = snd (C.toBoundary targetCorner)
      moveBoundary = cong qt κt ∙ βt

    sourcePath targetPath boundaryPath : I → Pointed ℓ-zero
    sourcePath i = Carrier (suc n) s , κs i
    targetPath i = Carrier (suc n) t , κt i
    boundaryPath i = CubeBoundary (suc n) , moveBoundary i

    sourceMap : (i : I) → sourcePath i →∙ boundaryPath i
    sourceMap i = qs , compPath→Square {p = cong qs κs} {q = moveBoundary}
      {r = anchorComparison (suc n) e h a} {s = βs} (sym square) i

    targetMap : (i : I) → targetPath i →∙ boundaryPath i
    targetMap i = qt , compPath→Square {p = cong qt κt} {q = moveBoundary}
      {r = refl} {s = βt} (lUnit moveBoundary) i

    TransitionPath : I → Type
    TransitionPath i = PointedOver (sourceMap i) (targetMap i)

    comparison-contractible : isContr (PathP TransitionPath
      (A.transitionAt a) (C.transition sourceCorner targetCorner))
    comparison-contractible = isProp→isContrPathP
      (λ i → isContr→isProp (pointed-over-contractible (sourceMap i) (targetMap i)
        (carrier-contractible (suc n) s h)))
      (A.transitionAt a) (C.transition sourceCorner targetCorner)

    comparison : A.transitionOver a ≡ cornerTransition
    comparison i =
      overMap {p = sourceMap i} {q = targetMap i} (fst comparison-contractible i) ,
      overMap-commutes {p = sourceMap i} {q = targetMap i} (fst comparison-contractible i)

  transition-comparison : (a : Anchor (suc n) t) → A.transitionOver a ≡ cornerTransition
  transition-comparison a = AtAnchor.comparison a

  weakening-comparison : A.weakeningOver ≡ cornerTransition
  weakening-comparison = transition-comparison (fst (anchor-contractible (suc n) t))

-- Contractibility applies to comparisons over the displayed path of
-- pointed presentations. It does not identify the projections of
-- comparisons built from different normalization seeds or inclusions.
