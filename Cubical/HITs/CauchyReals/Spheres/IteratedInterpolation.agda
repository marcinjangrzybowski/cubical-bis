module Cubical.HITs.CauchyReals.Spheres.IteratedInterpolation where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Interval using (Interval)
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Groups
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.MappingLifts
open import Cubical.HITs.CauchyReals.Spheres.Base
open import Cubical.HITs.CauchyReals.Spheres.InterpolationControl

module IteratedSphereInterpolation (m : ℕ) (x : RealSphere m) where
  private
    module C = SphereInterpolationControl m

  sphere∙ : PointedPremetricSpace ℓ-zero ℓ-zero
  sphere∙ = RealSphereSpace m , x

  admissiblePairs∙ : PointedPremetricSpace ℓ-zero ℓ-zero
  admissiblePairs∙ = C.AdmissiblePairs , ((x , x) , C.diagonal-admissible x)

  opaque
    interpolationFamily : BasedFamily Interval admissiblePairs∙ sphere∙
    interpolationFamily = C.interpolateUC , λ t →
      C.fixes-agreement t x x (C.diagonal-admissible x) refl

  -- A checked internal induction, for every loop depth and sphere
  -- dimension. Its source remains loops in the admissible-pair space.
  -- Identifying these with admissible pairs of nested sphere loops is a
  -- separate product/subspace comparison, not assumed by this theorem.
  opaque
    iteratedInterpolation : (n : ℕ) →
      BasedFamily Interval (realΩ^ n admissiblePairs∙) (realΩ^ n sphere∙)
    iteratedInterpolation n =
      iterateBasedFamily Interval n admissiblePairs∙ sphere∙ interpolationFamily
