module Cubical.HITs.CauchyReals.Circle.Winding.Angle where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Powerset
open import Cubical.Data.Sigma
open import Cubical.Data.NatPlusOne
open import Cubical.HITs.SetQuotients using (eq/)
open import Cubical.Data.Int.Fast as ℤ using (ℤ)
open import Cubical.Data.Rationals as ℚ using ([_/_])
import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ hiding (_^ⁿ_)
open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Bounds
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Order.AbsoluteValue
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition
open import Cubical.HITs.CauchyReals.Trigonometry.Base
open import Cubical.HITs.CauchyReals.Trigonometry.Pi
open import Cubical.HITs.CauchyReals.Circle.Core
open import Cubical.HITs.CauchyReals.Circle.Chart
open import Cubical.HITs.CauchyReals.Circle.Metric
open import Cubical.Tactics.CommRingSolver.Specialised.Reals

-- Angles are measured in turns, so the period is one.
opaque
  cover : ℝ → distCircle
  cover t = Circle→distCircle (injCircle t)

  cover-β : ∀ t → cover t ≡ Circle→distCircle (injCircle t)
  cover-β t = refl

cover-zero : cover 0 ≡ circle0
cover-zero = cover-β 0 ∙ injCircle0≡circle0

opaque
  unfolding cover circle+
  cover-add : ∀ s t → cover (s +ᵣ t) ≡ cover s ℝS¹.+ cover t
  cover-add s t = distCircle≡
    (cong cos (·DistR+ _ _ _) ∙ cosOfSum _ _)
    (cong sin (·DistR+ _ _ _) ∙ sinOfSum _ _ ∙ +ᵣComm _ _)

opaque
  unfolding cover
  cover-respects : ∀ s t → circle-rel s t → cover s ≡ cover t
  cover-respects s t related = cong Circle→distCircle (eq/ s t related)

opaque
  unfolding cover
  cover-effective : ∀ s t → cover s ≡ cover t → circle-rel s t
  cover-effective s t p = fromCircle≡ s t
    (invEq (congEquiv Circle≃distCircle) p)

-- Integer separation is used only after equality in the circle has
-- already supplied a unique integer witness.
cover-injective-near : ∀ s t → absᵣ (s -ᵣ t) <ᵣ 1 →
  cover s ≡ cover t → s ≡ t
cover-injective-near s t bound p =
  𝐑'.equalByDifference s t
    (snd k ∙ cong (λ z → rat [ z / 1 ]) k=0)
  where
  k = cover-effective s t p
  k=0 : fst k ≡ ℤ.pos 0
  k=0 = ℚ.distFromℤ (fst k) 0
    (<ᵣ→<ℚ _ _ (isTrans≡<ᵣ _ _ _
      (sym (absᵣ-rat _)
        ∙ cong absᵣ (sym (-ᵣ-rat₂ _ _))
        ∙ cong absᵣ (𝐑'.+IdR' _ _ (-ᵣ-rat 0))
        ∙ cong absᵣ (sym (snd k))) bound))

Near : distCircle → distCircle → Type
Near p q = cartDist² (fst p) (fst q) <ᵣ 2

private
  rotated : ∀ p q → Near p q →
    Σ distCircle λ z → 0 <ᵣ fst (fst z)
  rotated p q near = q ℝS¹.- p ,
    equivFun (cartDist≃upperHalf (q ℝS¹.- p))
      (snd (Iso.fun (rotateToOrigin 2 p) (q , near)))

opaque
  unfolding cover
  shortAngle : ∀ p q → Near p q → ℝ
  shortAngle p q near = fst (Iso.inv openHalfCircleIso (rotated p q near))

  shortAngle-bound : ∀ p q near →
    absᵣ (shortAngle p q near) <ᵣ rat [ 1 / 4 ]
  shortAngle-bound p q near = ointerval→abs< _ _
    (snd (Iso.inv openHalfCircleIso (rotated p q near)))

  shortAngle-cover : ∀ p q near →
    cover (shortAngle p q near) ≡ q ℝS¹.- p
  shortAngle-cover p q near =
    cong fst (Iso.sec openHalfCircleIso (rotated p q near))

shortAngle-step : ∀ p q near →
  p ℝS¹.+ cover (shortAngle p q near) ≡ q
shortAngle-step p q near =
  cong (p ℝS¹.+_) (shortAngle-cover p q near)
  ∙ ℝS¹.+Comm _ _ ∙ Iso.sec (rotationIso p) q

shortAngle-add : ∀ p q r pq qr pr →
  shortAngle p q pq +ᵣ shortAngle q r qr ≡ shortAngle p r pr
shortAngle-add p q r pq qr pr =
  cover-injective-near _ _ bound image
  where
  a = shortAngle p q pq
  b = shortAngle q r qr
  c = shortAngle p r pr

  bound : absᵣ ((a +ᵣ b) -ᵣ c) <ᵣ 1
  bound = isTrans≤<ᵣ _ _ _ (absᵣ-triangle'' _ _)
    (isTrans≤<ᵣ _ _ _ (≤ᵣ-+o _ _ _ (absᵣ-triangle a b))
      (isTrans<ᵣ _ (rat [ 1 / 4 ] +ᵣ rat [ 1 / 4 ] +ᵣ rat [ 1 / 4 ]) _
        (<ᵣMonotone+ᵣ _ _ _ _
          (<ᵣMonotone+ᵣ _ _ _ _ (shortAngle-bound p q pq) (shortAngle-bound q r qr))
          (shortAngle-bound p r pr))
        (isTrans≡<ᵣ _ _ _
          (cong (_+ᵣ rat [ 1 / 4 ]) (+ᵣ-rat _ _) ∙ +ᵣ-rat _ _)
          decℚ<ᵣ?)))

  image : cover (a +ᵣ b) ≡ cover c
  image = ℝS¹.·CancelL p
    (cong (p ℝS¹.+_) (cover-add a b)
      ∙ ℝS¹.+Assoc _ _ _
      ∙ cong (ℝS¹._+ cover b) (shortAngle-step p q pq)
      ∙ shortAngle-step q r qr
      ∙ sym (shortAngle-step p r pr))
