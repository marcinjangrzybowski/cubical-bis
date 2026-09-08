module Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.SquareAttachment where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (false; true)
open import Cubical.Data.Sigma
open import Cubical.HITs.Pushout.Base
open import Cubical.HITs.Pushout.PushoutProduct using (PushProd; _×̂_)
open import Cubical.Relation.Premetric.Base
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Interval using (𝟘; 𝟙)
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Base
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.ReflexiveGraph
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.DegenerateSquares
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.SquareBoundary
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.SquareDegeneracies
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.SquareFrames

module SquareAttachment {ℓ ℓ'} (X : PremetricSpace ℓ ℓ') where
  open Paths X
  open SquareDegeneracies X
  open SquareFrames X

  Realization₁ : Type (ℓ-max ℓ ℓ')
  Realization₁ = ReflexiveRealization (fst X) UCPath constantPath

  frameFilling : Frame → Type (ℓ-max ℓ ℓ')
  frameFilling (_ , verticals , horizontals) = Square {A = Realization₁}
    (edge (verticals false)) (edge (verticals true))
    (edge (horizontals false)) (edge (horizontals true))

  frameBoundary : Frame → Boundary₂ → Realization₁
  frameBoundary (_ , verticals , horizontals) = squareBoundary
    (edge (verticals false)) (edge (verticals true))
    (edge (horizontals false)) (edge (horizontals true))

  frameExtension : Frame → Type (ℓ-max ℓ ℓ')
  frameExtension f = Σ[ h ∈ (Disk₂ → Realization₁) ]
    ((b : Boundary₂) → h (boundary₂ b) ≡ frameBoundary f b)

  fillingExtension : (f : Frame) → frameFilling f → frameExtension f
  fillingExtension (_ , verticals , horizontals) = squareExtension
    (edge (verticals false)) (edge (verticals true))
    (edge (horizontals false)) (edge (horizontals true))

  horizontalFilling : (p : EdgeCube) → frameFilling (horizontalFrame p)
  horizontalFilling p = horizontalSquare (edge (p , refl , refl))
    (refl-edge (fst p 𝟘)) (refl-edge (fst p 𝟙))

  verticalFilling : (p : EdgeCube) → frameFilling (verticalFrame p)
  verticalFilling p = verticalSquare (edge (p , refl , refl))
    (refl-edge (fst p 𝟘)) (refl-edge (fst p 𝟙))

  constantFilling-coherence : (x : fst X) →
    horizontalFilling (constant x) ≡ verticalFilling (constant x)
  constantFilling-coherence x =
    constantSquare-coherence (edge (constantPath x)) (refl-edge x)

  -- Normalize the real face data before interpreting it synthetically.
  -- The coherence in the real frame transports the relative synthetic
  -- square coherence to the actual UC-square overlap.
  degenerateFilling : (l : Latching₂) → frameFilling (frame (latchingMap l))
  degenerateFilling (inl p) =
    subst frameFilling (horizontal-frame p) (horizontalFilling p)
  degenerateFilling (inr p) =
    subst frameFilling (vertical-frame p) (verticalFilling p)
  degenerateFilling (push x i) =
    subst frameFilling (constant-frame-coherence x i) (constantFilling-coherence x i)

  degenerateExtension : (l : Latching₂) → frameExtension (frame (latchingMap l))
  degenerateExtension l = fillingExtension (frame (latchingMap l)) (degenerateFilling l)

  boundaryMap : SquareCube → Boundary₂ → Realization₁
  boundaryMap s = frameBoundary (frame s)

  AttachmentBoundary₂ : Type (ℓ-max ℓ ℓ')
  AttachmentBoundary₂ = PushProd boundary₂ latchingMap

  -- An actual attaching map, including the intersection of degenerate
  -- interiors with all square boundaries. No coherence parameter remains.
  attach₂ : AttachmentBoundary₂ → Realization₁
  attach₂ (inl (b , s)) = boundaryMap s b
  attach₂ (inr (d , l)) = fst (degenerateExtension l) d
  attach₂ (push (b , l) i) = snd (degenerateExtension l) b (~ i)

  Realization₂ : Type (ℓ-max ℓ ℓ')
  Realization₂ = Pushout (boundary₂ ×̂ latchingMap) attach₂

  include₁ : Realization₁ → Realization₂
  include₁ = inr

  squareCell : SquareCube → Disk₂ → Realization₂
  squareCell s d = inl (d , s)

  square-boundary : (s : SquareCube) (b : Boundary₂) →
    squareCell s (boundary₂ b) ≡ include₁ (boundaryMap s b)
  square-boundary s b = push (inl (b , s))

  square-degenerate : (l : Latching₂) (d : Disk₂) →
    squareCell (latchingMap l) d ≡ include₁ (fst (degenerateExtension l) d)
  square-degenerate l d = push (inr (d , l))
