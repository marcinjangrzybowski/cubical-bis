module Cubical.HITs.CauchyReals.Spheres.Normalization where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma
open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness using (isSetℝ)
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Power.Base using (1^ⁿ)
open import Cubical.HITs.CauchyReals.Algebra.Inverse using (invℝ₊; invℝ₊1; x·invℝ₊[x])
open import Cubical.HITs.CauchyReals.Transcendental.Roots.Base using (root; nth-pow-root-iso; ^ⁿ∘root)
open import Cubical.HITs.CauchyReals.Spheres.Base
open import Cubical.HITs.CauchyReals.Spheres.Coordinates
open import Cubical.Tactics.CommRingSolver.Specialised.Reals

-- Only positive squared norms are needed for normalization.
positiveLength : (n : ℕ) (x : fst (Euclidean n)) → 0 <ᵣ norm² n x → ℝ₊
positiveLength n x positive = root 2 (norm² n x , positive)

positiveLength-square : (n : ℕ) (x : fst (Euclidean n)) (positive : 0 <ᵣ norm² n x) →
  fst (positiveLength n x positive) ·ᵣ fst (positiveLength n x positive) ≡ norm² n x
positiveLength-square n x positive =
  sym (x^²=x·x _) ∙ ^ⁿ∘root 2 (norm² n x , positive)

inverseLength : (n : ℕ) (x : fst (Euclidean n)) → 0 <ᵣ norm² n x → ℝ
inverseLength n x positive = fst (invℝ₊ (positiveLength n x positive))

normalizeCoordinates : (n : ℕ) (x : fst (Euclidean n)) →
  0 <ᵣ norm² n x → fst (Euclidean n)
normalizeCoordinates n x positive = scale n (inverseLength n x positive) x

opaque
  norm²-normalize : (n : ℕ) (x : fst (Euclidean n)) (positive : 0 <ᵣ norm² n x) →
    norm² n (normalizeCoordinates n x positive) ≡ 1
  norm²-normalize n x positive =
    norm²-scale n (inverseLength n x positive) x ∙
    cong (λ z → inverseLength n x positive ·ᵣ inverseLength n x positive ·ᵣ z)
      (sym (positiveLength-square n x positive)) ∙
    rearrange ∙ cong (λ z → z ·ᵣ z) (x·invℝ₊[x] (positiveLength n x positive)) ∙ ℝ!
    where
    r a : ℝ
    r = fst (positiveLength n x positive)
    a = inverseLength n x positive
    rearrange : (a ·ᵣ a) ·ᵣ (r ·ᵣ r) ≡ (r ·ᵣ a) ·ᵣ (r ·ᵣ a)
    rearrange = ℝ!

normalize : (m : ℕ) (x : fst (Euclidean (suc m))) →
  0 <ᵣ norm² (suc m) x → RealSphere m
normalize m x positive = normalizeCoordinates (suc m) x positive ,
  norm²-normalize (suc m) x positive

private
  root-two-one : root 2 (1 , decℚ<ᵣ?) ≡ (1 , decℚ<ᵣ?)
  root-two-one =
    cong (root 2) (ℝ₊≡ (sym (1^ⁿ 2))) ∙
    Iso.ret (nth-pow-root-iso 2) (1 , decℚ<ᵣ?)

positiveLength-sphere : (m : ℕ) (x : RealSphere m)
  (positive : 0 <ᵣ norm² (suc m) (fst x)) →
  positiveLength (suc m) (fst x) positive ≡ (1 , decℚ<ᵣ?)
positiveLength-sphere m x positive = cong (root 2) (ℝ₊≡ (snd x)) ∙ root-two-one

normalize-fixes-sphere : (m : ℕ) (x : RealSphere m)
  (positive : 0 <ᵣ norm² (suc m) (fst x)) → normalize m (fst x) positive ≡ x
normalize-fixes-sphere m x positive = Σ≡Prop (λ _ → isSetℝ _ _)
  (cong (λ a → scale (suc m) a (fst x))
    (cong (fst ∘ invℝ₊) (positiveLength-sphere m x positive) ∙ cong fst invℝ₊1) ∙
    scale-one (suc m) (fst x))
