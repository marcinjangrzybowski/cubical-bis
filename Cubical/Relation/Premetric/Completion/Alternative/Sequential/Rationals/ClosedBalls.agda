module Cubical.Relation.Premetric.Completion.Alternative.Sequential.Rationals.ClosedBalls where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma
open import Cubical.Data.Empty

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.Algebra.Ring

open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Inverse
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Rationals.Order as ℚ
  renaming (_<_ to _<ℚ_ ; _≤_ to _≤ℚ_)
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Rationals
open import Cubical.Relation.Premetric.Instances.Subspace
open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ
open OrderedCommRingStr (snd ℚOrderedCommRing)
open OrderedCommRingTheory ℚOrderedCommRing
open OrderedCommRingReasoning ℚOrderedCommRing

private
  module Pℚ = PremetricStr (ℚPremetricSpace .snd)
  module ℚRing = RingTheory (OrderedCommRing→Ring ℚOrderedCommRing)


-- This is deliberately a bounded-ball condition, not global uniform
-- continuity.  The modulus may depend on the ball, and its existence is
-- truncated so that no global choice of moduli is required.

record IsUniformlyContinuousOnBallWith
  (f : ℚ → ℚ) (B : ℚ₊) (μ : ℚ₊ → ℚ₊) : Type₀ where
  no-eta-equality
  field
    pres≈ : ∀ x y ε
      → abs x ≤ℚ fst B
      → abs y ≤ℚ fst B
      → x Pℚ.≈[ μ ε ] y
      → f x Pℚ.≈[ ε ] f y

open IsUniformlyContinuousOnBallWith

IsLocallyUniformlyContinuous : (ℚ → ℚ) → Type₀
IsLocallyUniformlyContinuous f = ∀ B →
  ∃[ μ ∈ (ℚ₊ → ℚ₊) ] IsUniformlyContinuousOnBallWith f B μ

isPropIsLocallyUniformlyContinuous : ∀ f →
  isProp (IsLocallyUniformlyContinuous f)
isPropIsLocallyUniformlyContinuous f = isPropΠ λ _ → squash₁


-- The same condition, presented intrinsically on the rational closed-ball
-- subspace rather than by passing the two membership proofs as arguments.

ClosedBallℚPredicate : ℚ₊ → ℙ ℚ
ClosedBallℚPredicate B q =
  (abs q ≤ℚ fst B) , ℚ.isProp≤ (abs q) (fst B)

ClosedBallℚPremetricSpace : ℚ₊ → PremetricSpace ℓ-zero ℓ-zero
ClosedBallℚPremetricSpace B =
  PremetricSubspace ℚPremetricSpace (ClosedBallℚPredicate B)

ClosedBallℚ : ℚ₊ → Type₀
ClosedBallℚ B = ⟨ ClosedBallℚPremetricSpace B ⟩

IsUniformlyContinuousOnClosedBallWith :
  (ℚ → ℚ) → ℚ₊ → (ℚ₊ → ℚ₊) → Type₀
IsUniformlyContinuousOnClosedBallWith f B μ =
  IsUniformlyContinuousWith
    (ClosedBallℚPremetricSpace B .snd) (f ∘ fst)
    (ℚPremetricSpace .snd) μ

onBallWith→onClosedBallWith : ∀ f B μ →
  IsUniformlyContinuousOnBallWith f B μ →
  IsUniformlyContinuousOnClosedBallWith f B μ
onBallWith→onClosedBallWith f B μ local
  .IsUniformlyContinuousWith.pres≈ x y ε x≈y =
  local .pres≈ (fst x) (fst y) ε (snd x) (snd y) x≈y

onClosedBallWith→onBallWith : ∀ f B μ →
  IsUniformlyContinuousOnClosedBallWith f B μ →
  IsUniformlyContinuousOnBallWith f B μ
onClosedBallWith→onBallWith f B μ local .pres≈
  x y ε absx≤B absy≤B x≈y =
  local .IsUniformlyContinuousWith.pres≈
    (x , absx≤B) (y , absy≤B) ε x≈y

IsUniformlyContinuousOnClosedBalls : (ℚ → ℚ) → Type₀
IsUniformlyContinuousOnClosedBalls f = ∀ B →
  ∃[ μ ∈ (ℚ₊ → ℚ₊) ]
    IsUniformlyContinuousOnClosedBallWith f B μ

isPropIsUniformlyContinuousOnClosedBalls : ∀ f →
  isProp (IsUniformlyContinuousOnClosedBalls f)
isPropIsUniformlyContinuousOnClosedBalls f = isPropΠ λ _ → squash₁

onClosedBalls→locallyUniformlyContinuous : ∀ f →
  IsUniformlyContinuousOnClosedBalls f →
  IsLocallyUniformlyContinuous f
onClosedBalls→locallyUniformlyContinuous f closed B =
  PT.map
    (λ { (μ , uc) → μ , onClosedBallWith→onBallWith f B μ uc })
    (closed B)

locallyUniformlyContinuous→onClosedBalls : ∀ f →
  IsLocallyUniformlyContinuous f →
  IsUniformlyContinuousOnClosedBalls f
locallyUniformlyContinuous→onClosedBalls f local B =
  PT.map
    (λ { (μ , uc) → μ , onBallWith→onClosedBallWith f B μ uc })
    (local B)

locallyUniformlyContinuous≃onClosedBalls : ∀ f →
  IsLocallyUniformlyContinuous f ≃
    IsUniformlyContinuousOnClosedBalls f
locallyUniformlyContinuous≃onClosedBalls f = propBiimpl→Equiv
  (isPropIsLocallyUniformlyContinuous f)
  (isPropIsUniformlyContinuousOnClosedBalls f)
  (locallyUniformlyContinuous→onClosedBalls f)
  (onClosedBalls→locallyUniformlyContinuous f)


-- Clamping to [-B,B] is non-expanding.  It turns one local modulus on B
-- into a global modulus for the clamped function.

clampBall : ℚ₊ → ℚ → ℚ
clampBall B = ℚ.clamp (ℚ.- fst B) (fst B)

clampBall-bounded : ∀ B q → abs (clampBall B q) ≤ℚ fst B
clampBall-bounded B q = ℚ.absFrom≤×≤ (fst B) (clampBall B q)
  (ℚ.≤clamp (ℚ.- fst B) (fst B) q
    (ℚ.isTrans≤ (ℚ.- fst B) 0 (fst B)
      (ℚ.-ℚ₊≤0 B) (ℚ.0≤ℚ₊ B)))
  (ℚ.clamp≤ (ℚ.- fst B) (fst B) q)

clampBall-pres≈ : ∀ B x y ε →
  x Pℚ.≈[ ε ] y → clampBall B x Pℚ.≈[ ε ] clampBall B y
clampBall-pres≈ B x y ε x≈y = ℚ.isTrans≤<
  (abs (clampBall B x ℚ.- clampBall B y))
  (abs (x ℚ.- y)) (fst ε)
  (ℚ.clampDist (ℚ.- fst B) (fst B) y x) x≈y

absToBounds : ∀ (B : ℚ₊) q → abs q ≤ℚ fst B →
  (ℚ.- fst B ≤ℚ q) × (q ≤ℚ fst B)
absToBounds B q absq≤B .fst =
  subst (ℚ.- fst B ≤ℚ_) (ℚ.-Invol q)
    (ℚ.minus-≤ (ℚ.- q) (fst B)
      (ℚ.isTrans≤ (ℚ.- q) (abs q) (fst B)
        (OrderedCommRingTheory.-≤abs ℚOrderedCommRing q) absq≤B))
absToBounds B q absq≤B .snd =
  ℚ.isTrans≤ q (abs q) (fst B)
    (OrderedCommRingTheory.≤abs ℚOrderedCommRing q) absq≤B

clampBall-fixes : ∀ B q → abs q ≤ℚ fst B → clampBall B q ≡ q
clampBall-fixes B q absq≤B =
  ℚ.inClamps (ℚ.- fst B) (fst B) q lowerBound upperBound
  where
  bounds : (ℚ.- fst B ≤ℚ q) × (q ≤ℚ fst B)
  bounds = absToBounds B q absq≤B

  lowerBound : ℚ.- fst B ≤ℚ q
  lowerBound = bounds .fst

  upperBound : q ≤ℚ fst B
  upperBound = bounds .snd


clamped-isUniformlyContinuousWith : ∀ f B μ →
  IsUniformlyContinuousOnBallWith f B μ →
  IsUniformlyContinuousWith
    (ℚPremetricSpace .snd) (f ∘ clampBall B)
    (ℚPremetricSpace .snd) μ
clamped-isUniformlyContinuousWith f B μ local
  .IsUniformlyContinuousWith.pres≈ x y ε x≈y =
  local .pres≈ (clampBall B x) (clampBall B y) ε
    (clampBall-bounded B x) (clampBall-bounded B y)
    (clampBall-pres≈ B x y (μ ε) x≈y)
