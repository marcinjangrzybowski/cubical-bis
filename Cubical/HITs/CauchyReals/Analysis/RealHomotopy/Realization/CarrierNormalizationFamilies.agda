module Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.CarrierNormalizationFamilies where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv using (equiv-proof)
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Sigma
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.CubicalShapes
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.SelectedFaceCarriers
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.CarrierCorners
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.CarrierAnchors
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.CarrierCornerNormalization

-- Evaluation over a contractible parameter space is an equivalence,
-- including for a dependent family of arbitrary higher types. Its
-- fiber retains the computation equation at the specified seed.
seededSections-contractible : ∀ {ℓA ℓP} {A : Type ℓA}
  (c : isContr A) (a₀ : A) (P : A → Type ℓP) (seed : P a₀) →
  isContr (Σ[ f ∈ ((a : A) → P a) ] f a₀ ≡ seed)
seededSections-contractible c a₀ P seed =
  equiv-proof (snd (Π-contractDom {B = P} (a₀ , isContr→isProp c a₀))) seed

module Normalize (n : ℕ) {s t : Selection (suc n)}
  (e : SelectionInclusion (suc n) s t) (h : HasSelectedFace (suc n) s)
  (v : DiscreteAnchor (suc n) t) where

  private
    ht = inclusion-inhabited (suc n) e h
    idt = selectionIdentity (suc n) t
    corner = discreteCorner (suc n) t v
    anchor₀ = discreteAnchor (suc n) t v
    cs = carrierCorner (suc n) s h corner
    ct = carrierCorner (suc n) t ht corner
    qs = carrierBoundaryMap (suc n) s
    qt = carrierBoundaryMap (suc n) t
    βs = carrierCorner-boundary n s h corner (inclusion-compatible (suc n) e v)
    βt = carrierCorner-boundary n t ht corner (inclusion-compatible (suc n) idt v)

  -- Normalize the ENTIRE span of boundary paths, retaining both carrier
  -- endpoint paths as data. The boundary equation is a higher type.
  Normalization : Anchor (suc n) t → Type
  Normalization a =
    Σ[ κs ∈ (anchorCarrier (suc n) e h a ≡ cs) ]
    Σ[ κt ∈ (anchorCarrier (suc n) idt ht a ≡ ct) ]
      anchorComparison (suc n) e h a ∙ (cong qt κt ∙ βt) ≡
      cong qs κs ∙ βs

  normalization-seed : Normalization anchor₀
  normalization-seed = corner-normalization (suc n) e h v ,
    corner-normalization (suc n) idt ht v , endpoint-normalization n e h v

  SeededNormalization : Type
  SeededNormalization = Σ[ f ∈ ((a : Anchor (suc n) t) → Normalization a) ]
    f anchor₀ ≡ normalization-seed

  seeded-normalization-contractible : isContr SeededNormalization
  seeded-normalization-contractible = seededSections-contractible
    (anchor-contractible (suc n) t) anchor₀ Normalization normalization-seed

  normalization : (a : Anchor (suc n) t) → Normalization a
  normalization = fst (fst seeded-normalization-contractible)

  normalization-at-seed : normalization anchor₀ ≡ normalization-seed
  normalization-at-seed = snd (fst seeded-normalization-contractible)

  -- All comparisons preserving the seed are controlled by the same
  -- fiber of evaluation. No independent higher naturality fields occur.
  normalization-comparisons : (f g : SeededNormalization) → isContr (f ≡ g)
  normalization-comparisons = isContr→isContrPath seeded-normalization-contractible

  -- Pulling back the WHOLE family retains every component of the square.
  -- This works for arbitrary cubical disks, boundaries, and face maps.
  along : ∀ {ℓD} {D : Type ℓD} (a : D → Anchor (suc n) t) →
    (x : D) → Normalization (a x)
  along a x = normalization (a x)

  along-restriction : ∀ {ℓB ℓD} {B : Type ℓB} {D : Type ℓD}
    (a : D → Anchor (suc n) t) (i : B → D) →
    (λ x → along a (i x)) ≡ along (λ x → a (i x))
  along-restriction a i = refl

-- This is one fixed inclusion and one fixed Boolean endpoint seed.
-- It does not construct prescribed normalization frames whose labels
-- or endpoint seeds vary across different carrier inclusions.
