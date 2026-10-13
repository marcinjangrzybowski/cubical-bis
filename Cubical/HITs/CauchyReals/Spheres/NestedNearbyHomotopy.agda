module Cubical.HITs.CauchyReals.Spheres.NestedNearbyHomotopy where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Interval
  using (Interval; IntervalSquare; 𝕀; 𝟘; 𝟙)
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Base
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.LoopGroup
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Groups
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product
open import Cubical.HITs.CauchyReals.Spheres.Base
open import Cubical.HITs.CauchyReals.Spheres.NestedInterpolation
open import Cubical.HITs.CauchyReals.Spheres.NestedInterpolationControl
open import Cubical.HITs.CauchyReals.Spheres.MetricCloseness
open CategoryStructures using (_∘UC_)

-- Extra parameters, including collar/homotopy coordinates, are retained
-- in ONE jointly UC map. Agreement is fixed at every parameter value.
module NestedNearbyMaps {ℓM ℓM'} {M : PremetricSpace ℓM ℓM'}
  (m : ℕ) (x : RealSphere m) (n : ℕ) where
  private
    module H = NestedSphereInterpolation m x
    module C = NestedControl m x

  module Between (f g : UC[ M , H.Space n ])
    (related : (u : fst M) → H.Rel n (fst f u) (fst g u)) where

    paired : UC[ M , H.Pairs n ]
    fst paired u = (fst f u , fst g u) , related u
    snd paired = PT.map
      (λ (μ , uc) → μ , isuniformlycontinuouswith (IsUniformlyContinuousWith.pres≈ uc))
      (snd (pairUC f g))

    deformation : UC[ PremetricProduct Interval M , H.Space n ]
    deformation = H.interpolateUC n ∘UC pairUC productFstUC (paired ∘UC productSndUC)

    at-start : (u : fst M) → fst deformation (𝟘 , u) ≡ fst f u
    at-start u = H.at-start n (fst f u) (fst g u) (related u)

    at-end : (u : fst M) → fst deformation (𝟙 , u) ≡ fst g u
    at-end u = H.at-end n (fst f u) (fst g u) (related u)

    fixes-agreement : (t : 𝕀) (u : fst M) → fst f u ≡ fst g u →
      fst deformation (t , u) ≡ fst f u
    fixes-agreement t u = H.fixes-agreement n t (fst f u) (fst g u) (related u)

    error-control : (ε δ : ℚ₊) → C.Control n ε δ →
      ((u : fst M) → C.Close n δ (fst f u) (fst g u)) →
      (t : 𝕀) (u : fst M) →
      C.Close n ε (fst deformation (t , u)) (fst f u) ×
      C.Close n ε (fst deformation (t , u)) (fst g u)
    error-control ε δ control close t u = control t (fst f u) (fst g u) (related u) (close u)

module NestedNearbyLoops (m : ℕ) (x : RealSphere m) (n : ℕ) where
  module H = NestedSphereInterpolation m x
  module C = NestedControl m x
  module G = Loops (H.Space n) (H.base n)
  private
    module S = SphereCloseness m

  -- This is the existing JOINTLY UC PathHomotopy, not merely a path in
  -- the uniform loop space. No general uncurrying theorem is used.
  homotopy : (p q : fst (H.Space (suc n))) → H.Rel (suc n) p q → G.PathHomotopy p q
  homotopy p q related = result
    where
    module D = NestedNearbyMaps.Between m x n (fst p) (fst q) related

    result : G.PathHomotopy p q
    G.PathHomotopy.deformation result = D.deformation
    G.PathHomotopy.at-start result = D.at-start
    G.PathHomotopy.at-end result = D.at-end
    G.PathHomotopy.fixes-start result t =
      D.fixes-agreement t 𝟘 (fst (snd p) ∙ sym (fst (snd q))) ∙ fst (snd p)
    G.PathHomotopy.fixes-end result t =
      D.fixes-agreement t 𝟙 (snd (snd p) ∙ sym (snd (snd q))) ∙ snd (snd p)

  nearby-homotopy : (δ : ℚ₊) → S.SafeRadius δ →
    (p q : fst (H.Space (suc n))) → C.Close (suc n) δ p q → G.PathHomotopy p q
  nearby-homotopy δ safe p q close = homotopy p q (C.safe-admissible δ safe (suc n) p q close)

  classOf : fst (H.Space (suc n)) → fst (realπGr n H.sphere∙)
  classOf p = Iso.fun (fst (realπGr-loopGroup n H.sphere∙)) (G.pathClass p)

  nearby-class : (δ : ℚ₊) → S.SafeRadius δ →
    (p q : fst (H.Space (suc n))) → C.Close (suc n) δ p q → classOf p ≡ classOf q
  nearby-class δ safe p q close = cong (Iso.fun (fst (realπGr-loopGroup n H.sphere∙)))
    (G.homotopy-class≡ (nearby-homotopy δ safe p q close))

  -- A uniform radius over the ENTIRE representative space exists in
  -- every degree. The same sphere radius can be used at all loop depths.
  classRadius : ∥ Σ[ δ ∈ ℚ₊ ] ((p q : fst (H.Space (suc n))) →
    C.Close (suc n) δ p q → classOf p ≡ classOf q) ∥₁
  classRadius = PT.map (λ (δ , safe) → δ , nearby-class δ safe) S.safeRadius
