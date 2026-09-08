module Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Realization.SquareBoundary where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool; false; true)
open import Cubical.Data.Sigma
open import Cubical.HITs.Interval.Base using ()
  renaming (Interval to 𝕁; zero to zeroJ; one to oneJ; seg to segJ)
open import Cubical.HITs.Pushout.Base
open import Cubical.HITs.Pushout.PushoutProduct using (PushProd; _×̂_)

endpoints : Bool → 𝕁
endpoints false = zeroJ
endpoints true = oneJ

Disk₂ : Type
Disk₂ = 𝕁 × 𝕁

Boundary₂ : Type
Boundary₂ = PushProd endpoints endpoints

boundary₂ : Boundary₂ → Disk₂
boundary₂ = endpoints ×̂ endpoints

pathMap : ∀ {ℓ} {A : Type ℓ} {x y : A} → x ≡ y → 𝕁 → A
pathMap {x = x} p zeroJ = x
pathMap {y = y} p oneJ = y
pathMap p (segJ i) = p i

module _ {ℓ} {A : Type ℓ}
  {a₀₀ a₀₁ a₁₀ a₁₁ : A}
  (left : a₀₀ ≡ a₀₁) (right : a₁₀ ≡ a₁₁)
  (bottom : a₀₀ ≡ a₁₀) (top : a₀₁ ≡ a₁₁) where

  squareBoundary : Boundary₂ → A
  squareBoundary (inl (false , t)) = pathMap left t
  squareBoundary (inl (true , t)) = pathMap right t
  squareBoundary (inr (t , false)) = pathMap bottom t
  squareBoundary (inr (t , true)) = pathMap top t
  squareBoundary (push (false , false) i) = a₀₀
  squareBoundary (push (false , true) i) = a₀₁
  squareBoundary (push (true , false) i) = a₁₀
  squareBoundary (push (true , true) i) = a₁₁

  squareInterior : Square left right bottom top → Disk₂ → A
  squareInterior s (zeroJ , t) = pathMap left t
  squareInterior s (oneJ , t) = pathMap right t
  squareInterior s (segJ i , zeroJ) = bottom i
  squareInterior s (segJ i , oneJ) = top i
  squareInterior s (segJ i , segJ j) = s i j

  squareRestriction : (s : Square left right bottom top) →
    (b : Boundary₂) → squareInterior s (boundary₂ b) ≡ squareBoundary b
  squareRestriction s (inl (false , t)) = refl
  squareRestriction s (inl (true , t)) = refl
  squareRestriction s (inr (zeroJ , false)) = refl
  squareRestriction s (inr (oneJ , false)) = refl
  squareRestriction s (inr (segJ i , false)) = refl
  squareRestriction s (inr (zeroJ , true)) = refl
  squareRestriction s (inr (oneJ , true)) = refl
  squareRestriction s (inr (segJ i , true)) = refl
  squareRestriction s (push (false , false) i) = refl
  squareRestriction s (push (false , true) i) = refl
  squareRestriction s (push (true , false) i) = refl
  squareRestriction s (push (true , true) i) = refl

  -- The restriction proof travels together with the chosen interior.
  squareExtension : Square left right bottom top →
    Σ[ h ∈ (Disk₂ → A) ] ((b : Boundary₂) → h (boundary₂ b) ≡ squareBoundary b)
  squareExtension s = squareInterior s , squareRestriction s
