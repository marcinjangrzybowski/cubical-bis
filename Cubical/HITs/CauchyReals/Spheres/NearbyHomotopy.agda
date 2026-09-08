module Cubical.HITs.CauchyReals.Spheres.NearbyHomotopy where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma
open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Interval using (Interval; 𝕀; 𝟘; 𝟙)
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Base
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Cubes
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product
open import Cubical.HITs.CauchyReals.Spheres.Base
open import Cubical.HITs.CauchyReals.Spheres.Interpolation
open import Cubical.HITs.CauchyReals.Spheres.UniformInterpolation
open CategoryStructures using (_∘UC_)

-- A single joint deformation works for any premetric domain. Agreement
-- is fixed pointwise, so relative conditions need no separate extension.
module NearbyMaps {ℓ ℓ'} {M : PremetricSpace ℓ ℓ'} (m : ℕ)
  (f g : UC[ M , RealSphereSpace m ])
  (close : ∀ u → squaredDistance (suc m) (fst (fst f u)) (fst (fst g u)) ≤ᵣ 2) where

  private
    module H = SphereInterpolation m productFstUC
      (f ∘UC productSndUC) (g ∘UC productSndUC)
      (λ (t , u) → close-spheres-dot-nonnegative m (fst f u) (fst g u) (close u))

  deformation : UC[ PremetricProduct Interval M , RealSphereSpace m ]
  deformation = H.interpolateUC

  at-start : ∀ u → fst deformation (𝟘 , u) ≡ fst f u
  at-start u = H.interpolate-start (𝟘 , u) refl

  at-end : ∀ u → fst deformation (𝟙 , u) ≡ fst g u
  at-end u = H.interpolate-end (𝟙 , u) refl

  fixes-agreement : ∀ t u → fst f u ≡ fst g u → fst deformation (t , u) ≡ fst f u
  fixes-agreement t u = H.interpolate-same (t , u)

module NearbyPaths (m : ℕ) where
  private
    module P = Paths (RealSphereSpace m)

  homotopy : ∀ {x y} (p q : P.UCPath x y) →
    (∀ t → squaredDistance (suc m) (fst (P.at p t)) (fst (P.at q t)) ≤ᵣ 2) →
    P.PathHomotopy p q
  homotopy p q close = result
    where
    module H = NearbyMaps m (fst p) (fst q) close

    result : P.PathHomotopy p q
    P.PathHomotopy.deformation result = H.deformation
    P.PathHomotopy.at-start result = H.at-start
    P.PathHomotopy.at-end result = H.at-end
    P.PathHomotopy.fixes-start result t =
      H.fixes-agreement t 𝟘 (fst (snd p) ∙ sym (fst (snd q))) ∙ fst (snd p)
    P.PathHomotopy.fixes-end result t =
      H.fixes-agreement t 𝟙 (snd (snd p) ∙ sym (snd (snd q))) ∙ snd (snd p)

-- Based real cubes retain their entire spatial boundary, in every degree.
module NearbyCubes (m k : ℕ) (x : RealSphere m) where
  private
    module B = BasedCubes (RealSphereSpace m) x

  module Deformation (p q : B.BasedCube k)
    (close : ∀ u → squaredDistance (suc m) (fst (B.atCube {n = k} p u))
      (fst (B.atCube {n = k} q u)) ≤ᵣ 2) where

    private
      module H = NearbyMaps m (fst p) (fst q) close

    open H public using (deformation; at-start; at-end)

    fixes-boundary : ∀ t u → OnBoundary k u → fst deformation (t , u) ≡ x
    fixes-boundary t u boundary =
      H.fixes-agreement t u (snd p u boundary ∙ sym (snd q u boundary)) ∙ snd p u boundary
