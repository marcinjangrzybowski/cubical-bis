module Cubical.HITs.CauchyReals.Spheres.NestedInterpolationControl where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Interval using (𝕀)
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.Groups using (loopLevel)
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Instances.FunctionSpace
open import Cubical.HITs.CauchyReals.Spheres.Base
open import Cubical.HITs.CauchyReals.Spheres.Interpolation using (close-spheres-dot-nonnegative)
open import Cubical.HITs.CauchyReals.Spheres.InterpolationControl
open import Cubical.HITs.CauchyReals.Spheres.MetricCloseness
open import Cubical.HITs.CauchyReals.Spheres.NestedInterpolation

-- Every depth is controlled by the SAME base interpolation modulus.
-- Only the requested output tolerance is halved at a loop successor.
module NestedControl (m : ℕ) (x : RealSphere m) where
  module H = NestedSphereInterpolation m x
  open H using (Space; Rel; interpolate; interpolate-zero; interpolate-successor)
  private
    module C = SphereInterpolationControl m
    module S = SphereCloseness m

  Close : (n : ℕ) → ℚ₊ → fst (Space n) → fst (Space n) → Type
  Close n ε p q = PremetricStr._≈[_]_ (snd (Space n)) p ε q

  safe-admissible : (δ : ℚ₊) → S.SafeRadius δ →
    (n : ℕ) (p q : fst (Space n)) → Close n δ p q → Rel n p q
  safe-admissible δ safe = H.L.close→related δ
    (λ p q close → close-spheres-dot-nonnegative m p q (safe p q close))

  Control : (n : ℕ) → ℚ₊ → ℚ₊ → Type (loopLevel n ℓ-zero ℓ-zero)
  Control n ε δ = (t : 𝕀) (p q : fst (Space n)) (h : Rel n p q) →
    Close n δ p q →
    Close n ε (interpolate n t p q h) p × Close n ε (interpolate n t p q h) q

  liftModulus : ℕ → (ℚ₊ → ℚ₊) → ℚ₊ → ℚ₊
  liftModulus zero μ ε = μ ε
  liftModulus (suc n) μ ε = liftModulus n μ (ε /2₊)

  lift-control : (n : ℕ) (μ : ℚ₊ → ℚ₊) →
    ((ε : ℚ₊) → C.InterpolationError ε (μ ε)) →
    (ε : ℚ₊) → Control n ε (liftModulus n μ ε)
  lift-control zero μ control ε t p q h close =
    subst (λ z → Close zero ε z p) (sym (interpolate-zero t p q h)) (fst result) ,
    subst (λ z → Close zero ε z q) (sym (interpolate-zero t p q h)) (snd result)
    where
    result = control ε t p q h close
  lift-control (suc n) μ control ε t p q h close =
    ∣ (ε /2₊ , /2₊<id ε , λ u →
      subst (λ z → Close n (ε /2₊) z (fst (fst p) u))
        (sym (interpolate-successor n t p q h u)) (fst (slice-control u))) ∣₁ ,
    ∣ (ε /2₊ , /2₊<id ε , λ u →
      subst (λ z → Close n (ε /2₊) z (fst (fst q) u))
        (sym (interpolate-successor n t p q h u)) (snd (slice-control u))) ∣₁
    where
    slice-control : (u : 𝕀) →
      Close n (ε /2₊) (interpolate n t (fst (fst p) u) (fst (fst q) u) (h u)) (fst (fst p) u) ×
      Close n (ε /2₊) (interpolate n t (fst (fst p) u) (fst (fst q) u) (h u)) (fst (fst q) u)
    slice-control u = lift-control n μ control (ε /2₊) t _ _ (h u)
      (≈→→pointwise 𝕀 (Space n) (fst (fst p)) (fst (fst q))
        (liftModulus n μ (ε /2₊)) close u)

  -- One map on a merely existing COMPLETE base modulus gives a complete
  -- modulus at any requested depth. No per-tolerance witnesses are chosen.
  errorModulus : (n : ℕ) →
    ∥ Σ[ μ ∈ (ℚ₊ → ℚ₊) ] ((ε : ℚ₊) → Control n ε (μ ε)) ∥₁
  errorModulus n = PT.map (λ (μ , control) → liftModulus n μ , lift-control n μ control)
    C.errorModulus

  controlledModulus : (n : ℕ) →
    ∥ Σ[ μ ∈ (ℚ₊ → ℚ₊) ] ((ε : ℚ₊) → S.SafeRadius (μ ε) × Control n ε (μ ε)) ∥₁
  controlledModulus n = PT.map2 combine S.safeRadius (errorModulus n)
    where
    combine : (Σ[ δ ∈ ℚ₊ ] S.SafeRadius δ) →
      (Σ[ μ ∈ (ℚ₊ → ℚ₊) ] ((ε : ℚ₊) → Control n ε (μ ε))) →
      Σ[ μ ∈ (ℚ₊ → ℚ₊) ] ((ε : ℚ₊) → S.SafeRadius (μ ε) × Control n ε (μ ε))
    combine (δ , safe) (μ , control) = (λ ε → min₊ δ (μ ε)) , λ ε →
      (λ p q close → safe p q (PremetricStr.isMonotone≈≤ (snd (RealSphereSpace m))
        p q _ _ (min₊≤L δ (μ ε)) close)) ,
      (λ t p q h close → control ε t p q h (PremetricStr.isMonotone≈≤ (snd (Space n))
        p q _ _ (min₊≤R δ (μ ε)) close))
