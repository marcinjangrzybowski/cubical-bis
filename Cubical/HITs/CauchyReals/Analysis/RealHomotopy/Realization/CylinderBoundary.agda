module Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.CylinderBoundary where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws using (cong-∙∙)
open import Cubical.Data.Bool using (Bool; false; true)
open import Cubical.Data.Sigma
open import Cubical.HITs.Interval.Base using ()
  renaming (Interval to 𝕁; zero to zero𝕁; one to one𝕁; seg to seg𝕁)
open import Cubical.HITs.Pushout.Base
open import Cubical.HITs.Pushout.PushoutProduct using (PushProd; _×̂_)
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.SquareBoundary
  using (endpoints)

-- One comparison for arbitrary boundary maps; no dimension index or
-- truncation is needed. It preserves the map into the cylinder disk.
module _ {ℓB ℓD} {B : Type ℓB} {D : Type ℓD} (b : B → D) where

  private
    P = PushProd endpoints b
    Q = Pushout b b

    p₀ : (y : B) → Path P (inl (false , b y)) (inr (zero𝕁 , y))
    p₀ y = push (false , y)

    p₁ : (y : B) → Path P (inl (true , b y)) (inr (one𝕁 , y))
    p₁ y = push (true , y)

    side : (y : B) → Path P (inr (zero𝕁 , y)) (inr (one𝕁 , y))
    side y i = inr (seg𝕁 i , y)

  collapseCylinder : P → Q
  collapseCylinder (inl (false , d)) = inl d
  collapseCylinder (inl (true , d)) = inr d
  collapseCylinder (inr (zero𝕁 , y)) = inl (b y)
  collapseCylinder (inr (one𝕁 , y)) = inr (b y)
  collapseCylinder (inr (seg𝕁 i , y)) = push y i
  collapseCylinder (push (false , y) i) = inl (b y)
  collapseCylinder (push (true , y) i) = inr (b y)

  expandCylinder : Q → P
  expandCylinder (inl d) = inl (false , d)
  expandCylinder (inr d) = inl (true , d)
  expandCylinder (push y i) = (p₀ y ∙∙ side y ∙∙ sym (p₁ y)) i

  private
    collapse-expand : (z : Q) → collapseCylinder (expandCylinder z) ≡ z
    collapse-expand (inl d) = refl
    collapse-expand (inr d) = refl
    collapse-expand (push y i) j =
      (cong-∙∙ collapseCylinder (p₀ y) (side y) (sym (p₁ y))
        ∙ sym (doubleCompPath-filler refl (push y) refl)) j i

    expand-collapse : (z : P) → expandCylinder (collapseCylinder z) ≡ z
    expand-collapse (inl (false , d)) = refl
    expand-collapse (inl (true , d)) = refl
    expand-collapse (inr (zero𝕁 , y)) = p₀ y
    expand-collapse (inr (one𝕁 , y)) = p₁ y
    expand-collapse (inr (seg𝕁 i , y)) j =
      doubleCompPath-filler (p₀ y) (side y) (sym (p₁ y)) (~ j) i
    expand-collapse (push (false , y) i) j = p₀ y (i ∧ j)
    expand-collapse (push (true , y) i) j = p₁ y (i ∧ j)

  cylinderBoundaryIso : Iso P Q
  cylinderBoundaryIso = iso collapseCylinder expandCylinder collapse-expand expand-collapse

  cylinderBoundaryMap : Q → 𝕁 × D
  cylinderBoundaryMap (inl d) = zero𝕁 , d
  cylinderBoundaryMap (inr d) = one𝕁 , d
  cylinderBoundaryMap (push y i) = seg𝕁 i , b y

  collapse-boundary : (z : P) →
    cylinderBoundaryMap (collapseCylinder z) ≡ (endpoints ×̂ b) z
  collapse-boundary (inl (false , d)) = refl
  collapse-boundary (inl (true , d)) = refl
  collapse-boundary (inr (zero𝕁 , y)) = refl
  collapse-boundary (inr (one𝕁 , y)) = refl
  collapse-boundary (inr (seg𝕁 i , y)) = refl
  collapse-boundary (push (false , y) i) = refl
  collapse-boundary (push (true , y) i) = refl
