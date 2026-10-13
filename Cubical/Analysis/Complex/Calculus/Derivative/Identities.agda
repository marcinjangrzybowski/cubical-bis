module Cubical.Analysis.Complex.Calculus.Derivative.Identities where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver

-- Pure remainder algebra. Keeping the ring abstract avoids normalizing
-- completed real values inside the solver.
module RemainderAlgebra {ℓ} (R : CommRing ℓ) where
  open CommRingStr (snd R)

  error : fst R → fst R → fst R → fst R → fst R
  error u v d h = (v - u) - d · h

  opaque
    add-error : ∀ u v a b d e h →
      error (u + a) (v + b) (d + e) h ≡ error u v d h + error a b e h
    add-error u v a b d e h = solve! R

    neg-error : ∀ u v d h → error (- u) (- v) (- d) h ≡ - error u v d h
    neg-error u v d h = solve! R

    product-error : ∀ u v a b d e h →
      error (u · a) (v · b) (d · a + u · e) h ≡
        (b · error u v d h + u · error a b e h) + d · ((b - a) · h)
    product-error u v a b d e h = solve! R

    chain-error : ∀ u v a b d e h →
      error a b (e · d) h ≡ error a b e (v - u) + e · error u v d h
    chain-error u v a b d e h = solve! R

    reconstruct : ∀ u v d h → error u v d h + d · h ≡ v - u
    reconstruct u v d h = solve! R
