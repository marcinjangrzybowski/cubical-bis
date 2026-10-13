module Cubical.Analysis.Complex.Series.Geometric.Algebra where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Algebra.CommRing
import Cubical.Algebra.Ring.Properties as Ring
open import Cubical.Tactics.CommRingSolver

-- The existing ordered-ring geometric theorem cannot be instantiated at
-- the complex ring. Only its elementary ring step is needed here.
module GeometricAlgebra {ℓ} (R : CommRing ℓ) where
  open CommRingStr (snd R)
  private module T = Ring.RingTheory (CommRing→Ring R)
  private module P = Exponentiation R

  opaque
    step : ∀ z p → (1r - p) + (1r - z) · p ≡ 1r - z · p
    step z p = solve! R

  opaque
    partialSumIdentity : ∀ z (sum : ℕ → fst R) → sum zero ≡ 0r →
      (∀ n → sum (suc n) ≡ sum n + (z P.^ n)) →
      ∀ n → (1r - z) · sum n ≡ 1r - (z P.^ n)
    partialSumIdentity z sum initial next zero = cong ((1r - z) ·_) initial
      ∙ T.0RightAnnihilates (1r - z) ∙ sym (+InvR 1r)
    partialSumIdentity z sum initial next (suc n) = cong ((1r - z) ·_) (next n)
      ∙ ·DistR+ (1r - z) (sum n) (z P.^ n)
      ∙ cong (_+ ((1r - z) · (z P.^ n))) (partialSumIdentity z sum initial next n)
      ∙ step z (z P.^ n)
