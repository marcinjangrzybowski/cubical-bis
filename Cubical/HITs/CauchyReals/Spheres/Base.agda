module Cubical.HITs.CauchyReals.Spheres.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Instances.Unit
open import Cubical.Relation.Premetric.Instances.Product
open import Cubical.Relation.Premetric.Instances.Subspace
open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Closeness using (isSetℝ)
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Analysis.Metric.Premetric
open import Cubical.HITs.CauchyReals.Analysis.RealHomotopy.LoopSpace
open import Cubical.Tactics.CommRingSolver.Specialised.Reals

-- Finite real coordinate spaces with their maximum-coordinate premetric.
-- The one- and two-coordinate cases are literally ℝ and ℝ × ℝ.
Euclidean : ℕ → PremetricSpace ℓ-zero ℓ-zero
Euclidean zero = UnitPremetricSpace
Euclidean (suc zero) = ℝPremetricSpace
Euclidean (suc (suc n)) = PremetricProduct ℝPremetricSpace (Euclidean (suc n))

norm² : (n : ℕ) → fst (Euclidean n) → ℝ
norm² zero _ = 0
norm² (suc zero) x = x ·ᵣ x
norm² (suc (suc n)) (x , xs) = x ·ᵣ x +ᵣ norm² (suc n) xs

origin : (n : ℕ) → fst (Euclidean n)
origin zero = tt
origin (suc zero) = 0
origin (suc (suc n)) = 0 , origin (suc n)

origin-norm² : (n : ℕ) → norm² n (origin n) ≡ 0
origin-norm² zero = refl
origin-norm² (suc zero) = ℝ!
origin-norm² (suc (suc n)) = cong (0 ·ᵣ 0 +ᵣ_) (origin-norm² (suc n)) ∙ ℝ!

-- S^n is the unit sphere in ℝ^(n+1), not a higher inductive type.
RealSphereSpace : ℕ → PremetricSpace ℓ-zero ℓ-zero
RealSphereSpace n = PremetricSubspace (Euclidean (suc n))
  (λ x → (norm² (suc n) x ≡ 1) , isSetℝ _ _)

RealSphere : ℕ → Type
RealSphere n = fst (RealSphereSpace n)

spherePoint : (n : ℕ) → RealSphere n
spherePoint zero = 1 , ℝ!
spherePoint (suc n) = (1 , origin (suc n)) ,
  (cong (1 ·ᵣ 1 +ᵣ_) (origin-norm² (suc n)) ∙ ℝ!)

RealSphere∙ : ℕ → PointedPremetricSpace ℓ-zero ℓ-zero
RealSphere∙ n = RealSphereSpace n , spherePoint n

isSetRealSphere : (n : ℕ) → isSet (RealSphere n)
isSetRealSphere n = PremetricStr.isSetM (snd (RealSphereSpace n))
