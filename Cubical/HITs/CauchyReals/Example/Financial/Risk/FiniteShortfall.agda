{-# OPTIONS --safe --cubical #-}

module Cubical.HITs.CauchyReals.Example.Financial.Risk.FiniteShortfall where

open import Cubical.HITs.CauchyReals.Example.Financial.Core.Finite
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.Shortfall
import Cubical.Data.FinData.Base as F

-- Applies equally to client claims, instrument cashflows, or scenario losses.
positivePart-sum-bound : ∀ {n} (X : Vector n) →
  positivePart (sum X) ≤ᵣ sum (λ i → positivePart (X i))
positivePart-sum-bound X = positivePart-upper _ _
  (sum-monotone X (λ i → positivePart (X i)) (λ i → ≤positivePart (X i)))
  (sum-nonnegative _ (λ i → positivePart-nonnegative (X i)))

-- Pooling claims and thresholds cannot exceed separately clamped shortfalls.
stopLoss-sum-bound : ∀ {n} (X C : Vector n) →
  stopLoss (sum X) (sum C) ≤ᵣ sum (λ i → stopLoss (X i) (C i))
stopLoss-sum-bound {zero} X C =
  ≡ᵣWeaken≤ᵣ _ _ (stopLoss-zero-below 0 0 (≤ᵣ-refl 0))
stopLoss-sum-bound {suc n} X C = isTrans≤ᵣ _ _ _
  (stopLoss-subadditive (X F.zero) (sum (λ i → X (F.suc i)))
    (C F.zero) (sum (λ i → C (F.suc i))))
  (≤ᵣMonotone+ᵣ _ _ _ _ (≤ᵣ-refl _)
    (stopLoss-sum-bound (λ i → X (F.suc i)) (λ i → C (F.suc i))))
