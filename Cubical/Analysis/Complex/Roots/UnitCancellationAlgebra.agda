module Cubical.Analysis.Complex.Roots.UnitCancellationAlgebra where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver

module UnitCancellation {ℓ} (R : CommRing ℓ) where
  open CommRingStr (snd R)

  cancelUnit : ∀ a b b′ → b · b′ ≡ 1r → a + b · ((- a) · b′) ≡ 0r
  cancelUnit a b b′ inverse = (solve! R)
    ∙ cong (λ t → a - a · t) inverse ∙ (solve! R)

  oppositeScaled : ∀ a b u v w → u + v · w ≡ 0r →
    a · u + b · (v · w) ≡ (a - b) · u
  oppositeScaled a b u v w cancel = (solve! R)
    ∙ cong (λ t → (a - b) · u + b · t) cancel ∙ (solve! R)
