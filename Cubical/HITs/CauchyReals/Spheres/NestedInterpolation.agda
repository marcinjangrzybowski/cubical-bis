module Cubical.HITs.CauchyReals.Spheres.NestedInterpolation where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CauchyReals.Foundation.Order.Base using (isProp≤ᵣ)
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Interval
  using (Interval; 𝕀; 𝟘; 𝟙)
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Groups
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.MappingLifts
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.PackedLoopFamilies
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.RelatedLoops
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product
open import Cubical.HITs.CauchyReals.Spheres.Base
open import Cubical.HITs.CauchyReals.Spheres.InterpolationControl
open CategoryStructures using (_∘UC_)

-- Binary interpolation on the ACTUAL iterated real loop spaces.
-- The admissibility condition is pointwise through all loop coordinates.
module NestedSphereInterpolation (m : ℕ) (x : RealSphere m) where
  private
    module C = SphereInterpolationControl m

  sphere∙ : PointedPremetricSpace ℓ-zero ℓ-zero
  sphere∙ = RealSphereSpace m , x

  module L = Related sphere∙ C.Admissible (λ p q → isProp≤ᵣ _ _) C.diagonal-admissible
  open L public using (Space; base; Rel; rel-prop; rel-refl; Pairs; pairs∙)

  opaque
    interpolationFamily : (n : ℕ) → BasedFamily Interval (pairs∙ n) (realΩ^ n sphere∙)
    fst (interpolationFamily zero) = fst C.interpolateUC ,
      PT.map (λ (μ , uc) → μ , isuniformlycontinuouswith (IsUniformlyContinuousWith.pres≈ uc))
        (snd C.interpolateUC)
    snd (interpolationFamily zero) t = C.fixes-agreement t x x (C.diagonal-admissible x) refl
    interpolationFamily (suc n) = Packed.family Interval (pairs∙ (suc n)) (pairs∙ n)
      (realΩ^ n sphere∙) (L.Step.packUC n) (L.Step.pack-based n) (interpolationFamily n)

  interpolateUC : (n : ℕ) → UC[ PremetricProduct Interval (Pairs n) , Space n ]
  interpolateUC n = fst (interpolationFamily n)

  interpolate : (n : ℕ) → 𝕀 → (p q : fst (Space n)) → Rel n p q → fst (Space n)
  interpolate n t p q h = fst (interpolateUC n) (t , ((p , q) , h))

  opaque
    unfolding interpolationFamily

    interpolate-zero : (t : 𝕀) (p q : RealSphere m) (h : Rel zero p q) →
      interpolate zero t p q h ≡ C.interpolate t p q h
    interpolate-zero t p q h = refl

    interpolate-successor : (n : ℕ) (t : 𝕀) (p q : fst (Space (suc n)))
      (h : Rel (suc n) p q) (u : 𝕀) →
      fst (fst (interpolate (suc n) t p q h)) u ≡
      interpolate n t (fst (fst p) u) (fst (fst q) u) (h u)
    interpolate-successor n t p q h u = Packed.family-β Interval (pairs∙ (suc n)) (pairs∙ n)
      (realΩ^ n sphere∙) (L.Step.packUC n) (L.Step.pack-based n) (interpolationFamily n)
      t ((p , q) , h) u

  at-start : (n : ℕ) (p q : fst (Space n)) (h : Rel n p q) → interpolate n 𝟘 p q h ≡ p
  at-start zero p q h = interpolate-zero 𝟘 p q h ∙ C.at-start p q h
  at-start (suc n) p q h = RealLoops.path-ext (Space n) (base n)
    (λ u → interpolate-successor n 𝟘 p q h u ∙ at-start n _ _ (h u))

  at-end : (n : ℕ) (p q : fst (Space n)) (h : Rel n p q) → interpolate n 𝟙 p q h ≡ q
  at-end zero p q h = interpolate-zero 𝟙 p q h ∙ C.at-end p q h
  at-end (suc n) p q h = RealLoops.path-ext (Space n) (base n)
    (λ u → interpolate-successor n 𝟙 p q h u ∙ at-end n _ _ (h u))

  fixes-diagonal : (n : ℕ) (t : 𝕀) (p : fst (Space n)) (h : Rel n p p) →
    interpolate n t p p h ≡ p
  fixes-diagonal zero t p h = interpolate-zero t p p h ∙ C.fixes-agreement t p p h refl
  fixes-diagonal (suc n) t p h = RealLoops.path-ext (Space n) (base n)
    (λ u → interpolate-successor n t p p h u ∙ fixes-diagonal n t _ (h u))

  fixes-agreement : (n : ℕ) (t : 𝕀) (p q : fst (Space n)) (h : Rel n p q) →
    p ≡ q → interpolate n t p q h ≡ p
  fixes-agreement n t p q h same =
    J (λ q same → (h : Rel n p q) → interpolate n t p q h ≡ p)
      (fixes-diagonal n t p) same h

  fixes-base : (n : ℕ) (t : 𝕀) →
    interpolate n t (base n) (base n) (rel-refl n (base n)) ≡ base n
  fixes-base n t = snd (interpolationFamily n) t
