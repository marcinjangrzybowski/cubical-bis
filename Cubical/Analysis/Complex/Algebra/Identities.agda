module Cubical.Analysis.Complex.Algebra.Identities where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver
import Cubical.Algebra.Ring.Properties as Ring

module Identities {ℓ} (R : CommRing ℓ) where
  open CommRingStr (snd R)

  shuffle : ∀ a b c d → (a + b) + (c + d) ≡ (a + c) + (b + d)
  shuffle = Ring.RingTheory.+ShufflePairs (CommRing→Ring R)

  productBoundExpansion : ∀ a b c d →
    (a · c + b · d) + (a · d + b · c) ≡ (a + b) · (c + d)
  productBoundExpansion a b c d = solve! R

  productDifference : ∀ a b c d → a · b - c · d ≡ (a - c) · b + c · (b - d)
  productDifference a b c d = solve! R

  sumDifference : ∀ a b c d → (a + b) - (c + d) ≡ (a - c) + (b - d)
  sumDifference a b c d = solve! R

  negativeDifference : ∀ a b → (- a) - (- b) ≡ - (a - b)
  negativeDifference a b = solve! R

  jointHornerBound : ∀ δ H B L →
    δ + (δ · H + B · (L · δ)) ≡ (1r + (H + B · L)) · δ
  jointHornerBound δ H B L = solve! R

  hornerDifference : ∀ a x y p q →
    (a + x · p) - (a + y · q) ≡ (x - y) · p + y · (p - q)
  hornerDifference a x y p q = solve! R

  subtractSameRight : ∀ a b c → (a - c) - (b - c) ≡ a - b
  subtractSameRight a b c = solve! R

  linearStep : ∀ a r x p → (- r) · a + x · (a + (x - r) · p) ≡
    (x - r) · (a + x · p)
  linearStep a r x p = solve! R
