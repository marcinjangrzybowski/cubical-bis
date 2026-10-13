module Cubical.Analysis.Complex.Modulus.DistanceAlgebra where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver
import Cubical.Algebra.Ring.Properties as Ring

-- Keep the finite ring calculations abstract, so metric estimates do not
-- normalize arithmetic on the native completed real carrier.
module DistanceAlgebra {ℓ} (R : CommRing ℓ) where
  open CommRingStr (snd R)

  difference-chain : ∀ a b c → a - c ≡ (a - b) + (b - c)
  difference-chain a b c = solve! R

  difference-opposite : ∀ a b → a - b ≡ - (b - a)
  difference-opposite a b = solve! R

  middle-first : ∀ a b c → a + (b + c) ≡ b + (a + c)
  middle-first = Ring.RingTheory.+Assoc-comm1 (CommRing→Ring R)
