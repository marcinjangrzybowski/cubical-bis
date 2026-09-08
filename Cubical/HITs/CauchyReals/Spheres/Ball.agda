module Cubical.HITs.CauchyReals.Spheres.Ball where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Subspace
open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals
open import Cubical.HITs.CauchyReals.Foundation.Closeness using (isSetℝ)
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Spheres.Base

-- The closed Euclidean unit ball, with the same coordinate premetric as
-- the spheres. Its boundary in dimension n+1 is the real n-sphere.
RealBallSpace : ℕ → PremetricSpace ℓ-zero ℓ-zero
RealBallSpace n = PremetricSubspace (Euclidean n)
  (λ v → (norm² n v ≤ᵣ 1) , isProp≤ᵣ _ _)

RealBall : ℕ → Type
RealBall n = fst (RealBallSpace n)

ballCenter : (n : ℕ) → RealBall n
ballCenter n = origin n , subst (_≤ᵣ 1) (sym (origin-norm² n)) decℚ≤ᵣ?

BallBoundarySpace : ℕ → PremetricSpace ℓ-zero ℓ-zero
BallBoundarySpace n = PremetricSubspace (RealBallSpace n)
  (λ b → (norm² n (fst b) ≡ 1) , isSetℝ _ _)

private
  sphere-bound : (n : ℕ) (s : RealSphere n) → norm² (suc n) (fst s) ≤ᵣ 1
  sphere-bound n s = subst (_≤ᵣ 1) (sym (snd s)) decℚ≤ᵣ?

sphereIntoBall : (n : ℕ) → NE[ RealSphereSpace n , RealBallSpace (suc n) ]
fst (sphereIntoBall n) s = fst s , sphere-bound n s
IsNonExpanding.pres≈ (snd (sphereIntoBall n)) s t ε = idfun _

sphereBallBoundaryIso : (n : ℕ) → Iso (RealSphere n) (fst (BallBoundarySpace (suc n)))
Iso.fun (sphereBallBoundaryIso n) s = fst (sphereIntoBall n) s , snd s
Iso.inv (sphereBallBoundaryIso n) (b , onBoundary) = fst b , onBoundary
Iso.sec (sphereBallBoundaryIso n) (b , onBoundary) =
  Σ≡Prop (λ _ → isSetℝ _ _) (Σ≡Prop (λ v → isProp≤ᵣ _ _) refl)
Iso.ret (sphereBallBoundaryIso n) s = refl
