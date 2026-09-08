module Cubical.HITs.CauchyReals.Spheres.InterpolationControl where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Interval
  using (Interval; 𝕀; 𝟘; 𝟙)
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product
open import Cubical.Relation.Premetric.Instances.Subspace
open import Cubical.HITs.CauchyReals.Spheres.Base
open import Cubical.HITs.CauchyReals.Spheres.Coordinates
open import Cubical.HITs.CauchyReals.Spheres.Interpolation
open import Cubical.HITs.CauchyReals.Spheres.UniformInterpolation
open import Cubical.HITs.CauchyReals.Spheres.MetricCloseness
open CategoryStructures using (_∘UC_)

-- One operator and one merely existing modulus work for all admissible
-- pairs and all real times, uniformly in sphere dimension.
module SphereInterpolationControl (m : ℕ) where
  private
    S = RealSphereSpace m
    module PS = PremetricStr (snd S)
    module PI = PremetricStr (snd Interval)
    module C = SphereCloseness m

  Admissible : RealSphere m → RealSphere m → Type
  Admissible x y = 0 ≤ᵣ dot (suc m) (fst x) (fst y)

  AdmissiblePairs : PremetricSpace ℓ-zero ℓ-zero
  AdmissiblePairs = PremetricSubspace (PremetricProduct S S)
    (λ (x , y) → Admissible x y , isProp≤ᵣ _ _)

  private
    inclusion : UC[ AdmissiblePairs , PremetricProduct S S ]
    inclusion = subspaceInclusionUC (PremetricProduct S S)
      (λ (x , y) → Admissible x y , isProp≤ᵣ _ _)

    module U = SphereInterpolation m productFstUC
      (productFstUC ∘UC (inclusion ∘UC productSndUC))
      (productSndUC ∘UC (inclusion ∘UC productSndUC))
      (λ u → snd (snd u))

  -- Seal the normalization implementation so applying the operator does
  -- not unfold its large continuity and nonvanishing proofs downstream.
  opaque
    interpolateUC : UC[ PremetricProduct Interval AdmissiblePairs , S ]
    interpolateUC = U.interpolateUC

  interpolate : 𝕀 → (x y : RealSphere m) → Admissible x y → RealSphere m
  interpolate t x y h = fst interpolateUC (t , ((x , y) , h))

  opaque
    unfolding interpolateUC

    at-start : (x y : RealSphere m) (h : Admissible x y) →
      interpolate 𝟘 x y h ≡ x
    at-start x y h = U.interpolate-start (𝟘 , ((x , y) , h)) refl

    at-end : (x y : RealSphere m) (h : Admissible x y) →
      interpolate 𝟙 x y h ≡ y
    at-end x y h = U.interpolate-end (𝟙 , ((x , y) , h)) refl

    fixes-agreement : (t : 𝕀) (x y : RealSphere m) (h : Admissible x y) →
      x ≡ y → interpolate t x y h ≡ x
    fixes-agreement t x y h = U.interpolate-same (t , ((x , y) , h))

  diagonal-admissible : (x : RealSphere m) → Admissible x x
  diagonal-admissible x = subst (0 ≤ᵣ_)
    (sym (dot-self (suc m) (fst x) ∙ snd x)) decℚ≤ᵣ?

  -- Closeness of the inputs controls the whole interpolating path.
  -- The bound is independent of time, the pair, and any parameter domain.
  InterpolationError : ℚ₊ → ℚ₊ → Type
  InterpolationError ε δ = (t : 𝕀) (x y : RealSphere m)
    (h : Admissible x y) → x PS.≈[ δ ] y →
    (interpolate t x y h PS.≈[ ε ] x) ×
    (interpolate t x y h PS.≈[ ε ] y)

  errorModulus : ∥ Σ[ μ ∈ (ℚ₊ → ℚ₊) ] ((ε : ℚ₊) → InterpolationError ε (μ ε)) ∥₁
  errorModulus = PT.map build (snd interpolateUC)
    where
    build : (Σ[ μ ∈ (ℚ₊ → ℚ₊) ] IsUniformlyContinuousWith
      (snd (PremetricProduct Interval AdmissiblePairs))
      (fst interpolateUC) (snd S) μ) →
      Σ[ μ ∈ (ℚ₊ → ℚ₊) ] ((ε : ℚ₊) → InterpolationError ε (μ ε))
    build (μ , uc) = μ , control
      where
      control : (ε : ℚ₊) → InterpolationError ε (μ ε)
      control ε t x y h close =
        subst (interpolate t x y h PS.≈[ ε ]_)
          (fixes-agreement t x x (diagonal-admissible x) refl)
          (IsUniformlyContinuousWith.pres≈ uc
            (t , ((x , y) , h)) (t , ((x , x) , diagonal-admissible x)) ε
            (PI.isRefl≈ t (μ ε) , PS.isRefl≈ x (μ ε) , PS.isSym≈ x y (μ ε) close))
        , subst (interpolate t x y h PS.≈[ ε ]_)
          (fixes-agreement t y y (diagonal-admissible y) refl)
          (IsUniformlyContinuousWith.pres≈ uc
            (t , ((x , y) , h)) (t , ((y , y) , diagonal-admissible y)) ε
            (PI.isRefl≈ t (μ ε) , close , PS.isRefl≈ y (μ ε)))

  -- Combine two already existing witnesses inside one truncation. This
  -- chooses no new radius separately at each requested tolerance.
  controlledModulus : ∥ Σ[ μ ∈ (ℚ₊ → ℚ₊) ] ((ε : ℚ₊) →
    C.SafeRadius (μ ε) × InterpolationError ε (μ ε)) ∥₁
  controlledModulus = PT.map2 combine C.safeRadius errorModulus
    where
    combine : (Σ[ δ ∈ ℚ₊ ] C.SafeRadius δ) →
      (Σ[ μ ∈ (ℚ₊ → ℚ₊) ] ((ε : ℚ₊) → InterpolationError ε (μ ε))) →
      Σ[ μ ∈ (ℚ₊ → ℚ₊) ] ((ε : ℚ₊) →
        C.SafeRadius (μ ε) × InterpolationError ε (μ ε))
    combine (δ , safe) (μ , control) = (λ ε → min₊ δ (μ ε)) , λ ε →
      (λ x y close → safe x y
        (PS.isMonotone≈≤ x y _ _ (min₊≤L δ (μ ε)) close)) ,
      (λ t x y h close → control ε t x y h
        (PS.isMonotone≈≤ x y _ _ (min₊≤R δ (μ ε)) close))
