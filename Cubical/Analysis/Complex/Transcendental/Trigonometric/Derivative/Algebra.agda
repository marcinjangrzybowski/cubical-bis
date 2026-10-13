module Cubical.Analysis.Complex.Transcendental.Trigonometric.Derivative.Algebra where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver
import Cubical.Analysis.Complex.Transcendental.Trigonometric.Algebra as Algebra

-- Simplify the derivatives of the two exponential formulas in an abstract
-- ring; the only special fact about the imaginary unit is its square.
module EulerDerivativeAlgebra {ℓ} (R : CommRing ℓ) where
  open CommRingStr (snd R)
  open Algebra.EulerAlgebra R

  opaque
    cosPair-derivative : ∀ h j a b →
      h · (a · j + b · (- j)) ≡ - sinPair h j a b
    cosPair-derivative h j a b = solve! R

    sinPair-derivative : ∀ h j → j · j ≡ - 1r → ∀ a b →
      (- j · h) · (a · j - b · (- j)) ≡ cosPair h a b
    sinPair-derivative h j square a b =
      (- j · h) · (a · j - b · (- j))
        ≡⟨ solve! R ⟩
      - (j · j) · (h · (a + b))
        ≡⟨ cong (λ t → - t · (h · (a + b))) square ⟩
      - (- 1r) · (h · (a + b))
        ≡⟨ solve! R ⟩
      cosPair h a b ∎
