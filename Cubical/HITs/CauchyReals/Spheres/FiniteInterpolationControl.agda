module Cubical.HITs.CauchyReals.Spheres.FiniteInterpolationControl where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isPropΠ)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open 1/2∈ℚ using (/2+/2≡id)
open import Cubical.HITs.CauchyReals.Foundation.Base using (ℝ; rat)
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.PathGroupoid.Interval using (𝕀)
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.FiniteStitching
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.InterpolationClocks
open import Cubical.Relation.Premetric.Base
open import Cubical.HITs.CauchyReals.Spheres.Base
open import Cubical.HITs.CauchyReals.Spheres.NestedInterpolationControl
open import Cubical.HITs.CauchyReals.Spheres.FiniteInterpolation

module PolygonControl (m : ℕ) (x : RealSphere m) (n : ℕ) where
  module S = SpherePolygons m x n
  module C = NestedControl m x
  open S using (Polygon; endpoint; startpoint; branch; chain; pathUC; loop)
  module A = PremetricStr (snd (S.H.Space n))

  sampleRadius : ℚ₊ → ℚ₊ → ℚ₊
  sampleRadius ε δ = min₊ (δ /2₊) ((ε /2₊) /2₊)

  local-error : (ε δ : ℚ₊) → C.Control n ((ε /2₊) /2₊) δ →
    (t : 𝕀) (p q r : fst (S.H.Space n)) (h : S.H.Rel n p q) →
    C.Close n (sampleRadius ε δ) p r → C.Close n (sampleRadius ε δ) q r →
    C.Close n (ε /2₊) (S.H.interpolate n t p q h) r
  local-error ε δ control t p q r h pr qr =
    A.subst≈ _ r (/2+/2≡id (fst (ε /2₊)))
      (A.isTriangular≈ _ p r ((ε /2₊) /2₊) ((ε /2₊) /2₊)
        (fst (control t p q h diameter))
        (A.isMonotone≈≤ p r (sampleRadius ε δ) ((ε /2₊) /2₊)
          (min₊≤R (δ /2₊) ((ε /2₊) /2₊)) pr))
    where
    diameter : C.Close n δ p q
    diameter = A.subst≈ p q (/2+/2≡id (fst δ))
      (A.isTriangular≈ p r q (δ /2₊) (δ /2₊)
        (A.isMonotone≈≤ p r (sampleRadius ε δ) (δ /2₊)
          (min₊≤L (δ /2₊) ((ε /2₊) /2₊)) pr)
        (A.isSym≈ q r (δ /2₊)
          (A.isMonotone≈≤ q r (sampleRadius ε δ) (δ /2₊)
            (min₊≤L (δ /2₊) ((ε /2₊) /2₊)) qr)))

  -- The sample bounds are required only on the actual branch regions.
  -- They are the geometric input still to be supplied by a fine mesh.
  module Against (f : ℝ → fst (S.H.Space n)) (ε δ : ℚ₊)
    (control : C.Control n ((ε /2₊) /2₊) δ) where
    private
      η = sampleRadius ε δ
      module Q = S.P.Property (λ (z , unit) p → rat start ≤ᵣ z → C.Close n (ε /2₊) p (f z))
        (λ (z , unit) p → isPropΠ (λ _ → A.isProp≈ p (f z) (ε /2₊)))

    Accuracy : (k : ℕ) → Polygon k → Type
    Accuracy zero ((p , q) , h) = (z : ℝ) → rat start ≤ᵣ z → z <ᵣ rat (upper zero) →
      C.Close n η p (f z) × C.Close n η q (f z)
    Accuracy (suc k) (c , q , h) = Accuracy k c ×
      ((z : ℝ) → rat start ≤ᵣ z → rat (cut k) <ᵣ z → z <ᵣ rat (upper (suc k)) →
        C.Close n η (endpoint k c) (f z) × C.Close n η q (f z))

    branchwise : (k : ℕ) (c : Polygon k) → Accuracy k c → Q.Branchwise k (chain k c)
    branchwise zero ((p , q) , h) good z unit hi lower =
      local-error ε δ control (clock zero z) p q (f z) h (fst (good z lower hi)) (snd (good z lower hi))
    branchwise (suc k) (c , q , h) (previous , good) = branchwise k c previous ,
      λ z unit lo hi lower → local-error ε δ control (clock (suc k) z) (endpoint k c) q (f z) h
        (fst (good z lower lo hi)) (snd (good z lower lo hi))

    path-error : (k : ℕ) (c : Polygon k) → Accuracy k c → (t : 𝕀) →
      C.Close n (ε /2₊) (fst (pathUC k c) t) (f (fst (stretchUC k) t))
    path-error k c good t = Q.paste-property k (chain k c) (branchwise k c good)
      (fst (stretchUC k) t) tt (stretch-before k t) (stretch-lower k t)

    loop-error : (k : ℕ) (c : Polygon k) (at0 : startpoint k c ≡ S.H.base n)
      (at1 : endpoint k c ≡ S.H.base n) (p : fst (S.H.Space (suc n))) →
      ((t : 𝕀) → f (fst (stretchUC k) t) ≡ fst (fst p) t) → Accuracy k c →
      C.Close (suc n) ε (loop k c at0 at1) p
    loop-error k c at0 at1 p recovers good = ∣ (ε /2₊ , /2₊<id ε , λ t →
      subst (C.Close n (ε /2₊) (fst (pathUC k c) t)) (recovers t) (path-error k c good t)) ∣₁

    -- This is exactly the kind of witness consumed by JointDensity.
    -- What remains is to construct the finite samples and Accuracy.
    approximant : (k : ℕ) (c : Polygon k) (at0 : startpoint k c ≡ S.H.base n)
      (at1 : endpoint k c ≡ S.H.base n) (p : fst (S.H.Space (suc n))) →
      ((t : 𝕀) → f (fst (stretchUC k) t) ≡ fst (fst p) t) →
      S.JointVertices k c → Accuracy k c →
      Σ[ q ∈ fst (S.H.Space (suc n)) ] S.J.Joint (suc n) q × C.Close (suc n) ε p q
    approximant k c at0 at1 p recovers joint good = loop k c at0 at1 ,
      S.loop-joint k c at0 at1 joint ,
      PremetricStr.isSym≈ (snd (S.H.Space (suc n))) (loop k c at0 at1) p ε
        (loop-error k c at0 at1 p recovers good)
