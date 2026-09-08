module Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.SquareFrames where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Bool using (Bool; false; true)
open import Cubical.Data.Sigma
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Interval
  using (Interval; 𝕀; 𝟘; 𝟙)
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Real using (constantUC)
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Base
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.SquareDegeneracies
open CategoryStructures using (_∘UC_; idᵘᶜ)

realEndpoint : Bool → 𝕀
realEndpoint false = 𝟘
realEndpoint true = 𝟙

module SquareFrames {ℓ ℓ'} (X : PremetricSpace ℓ ℓ') where
  open Paths X
  open SquareDegeneracies X
  private
    module PX = PremetricStr (snd X)

  Corners : Type ℓ
  Corners = Bool → Bool → fst X

  VerticalEdges HorizontalEdges : Corners → Type (ℓ-max ℓ ℓ')
  VerticalEdges v = (b : Bool) → UCPath (v b false) (v b true)
  HorizontalEdges v = (b : Bool) → UCPath (v false b) (v true b)

  -- These are real data, before applying the synthetic edge constructor.
  Frame : Type (ℓ-max ℓ ℓ')
  Frame = Σ[ v ∈ Corners ] VerticalEdges v × HorizontalEdges v

  isSetFrame : isSet Frame
  isSetFrame = isSetΣ (isSetΠ (λ _ → isSetΠ (λ _ → PX.isSetM)))
    (λ v → isSet× (isSetΠ (λ b → isSetUCPath (v b false) (v b true)))
                   (isSetΠ (λ b → isSetUCPath (v false b) (v true b))))

  private
    framePath : {v : Corners} {l₀ l₁ : VerticalEdges v} {b₀ b₁ : HorizontalEdges v} →
      ((e : Bool) (t : 𝕀) → at (l₀ e) t ≡ at (l₁ e) t) →
      ((e : Bool) (t : 𝕀) → at (b₀ e) t ≡ at (b₁ e) t) →
      Path Frame (v , l₀ , b₀) (v , l₁ , b₁)
    framePath {v = v} {l₀} {l₁} {b₀} {b₁} left-same bottom-same i = v ,
      (λ e → path-ext {p = l₀ e} {q = l₁ e} (left-same e) i) ,
      (λ e → path-ext {p = b₀ e} {q = b₁ e} (bottom-same e) i)

  verticalFace horizontalFace : SquareCube → Bool → EdgeCube
  verticalFace s b = s ∘UC pairUC (constantUC (realEndpoint b)) idᵘᶜ
  horizontalFace s b = s ∘UC pairUC idᵘᶜ (constantUC (realEndpoint b))

  frame : SquareCube → Frame
  frame s = (λ b c → fst s (realEndpoint b , realEndpoint c)) ,
    (λ b → verticalFace s b , refl , refl) ,
    (λ b → horizontalFace s b , refl , refl)

  horizontalFrame verticalFrame : EdgeCube → Frame
  horizontalFrame p = (λ b _ → fst p (realEndpoint b)) ,
    (λ b → constantPath (fst p (realEndpoint b))) , (λ _ → p , refl , refl)
  verticalFrame p = (λ _ b → fst p (realEndpoint b)) ,
    (λ _ → p , refl , refl) , (λ b → constantPath (fst p (realEndpoint b)))

  constantFrame : fst X → Frame
  constantFrame x = (λ _ _ → x) , (λ _ → constantPath x) , (λ _ → constantPath x)

  horizontal-frame : (p : EdgeCube) → horizontalFrame p ≡ frame (horizontal p)
  horizontal-frame p = framePath (λ _ _ → refl) (λ _ _ → refl)

  vertical-frame : (p : EdgeCube) → verticalFrame p ≡ frame (vertical p)
  vertical-frame p = framePath (λ _ _ → refl) (λ _ _ → refl)

  -- The two face-normalization paths agree over the constant-square
  -- overlap because the REAL frame is a set. No synthetic target is
  -- required to be a set.
  constant-frame-coherence : (x : fst X) →
    PathP (λ i → constantFrame x ≡ frame (constant-square x i))
      (horizontal-frame (constant x)) (vertical-frame (constant x))
  constant-frame-coherence x = isProp→PathP
    (λ i → isSetFrame (constantFrame x) (frame (constant-square x i)))
    (horizontal-frame (constant x)) (vertical-frame (constant x))
