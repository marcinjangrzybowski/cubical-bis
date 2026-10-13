module Cubical.Analysis.Complex.Transcendental.Trigonometric.Algebra where

-- Algebra of the two exponential values. Work over an abstract ring so
-- solver normalization never expands the native completed real functions.
open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver
import Cubical.Analysis.Complex.Algebra.Cartesian as Cartesian

module EulerAlgebra {ℓ} (R : CommRing ℓ) where
  open CommRingStr (snd R)

  cosPair : fst R → fst R → fst R → fst R
  cosPair h a b = h · (a + b)

  sinPair : fst R → fst R → fst R → fst R → fst R
  sinPair h j a b = (- j · h) · (a - b)

  opaque
    cosPair-swap : ∀ h a b → cosPair h b a ≡ cosPair h a b
    cosPair-swap h a b = cong (h ·_) (+Comm b a)

    sinPair-swap : ∀ h j a b → sinPair h j b a ≡ - sinPair h j a b
    sinPair-swap h j a b = solve! R

    cosPair-one : ∀ h → h + h ≡ 1r → cosPair h 1r 1r ≡ 1r
    cosPair-one h half = (solve! R) ∙ half

    sinPair-same : ∀ h j a → sinPair h j a a ≡ 0r
    sinPair-same h j a = solve! R

    euler : ∀ h j → h + h ≡ 1r → j · j ≡ - 1r → ∀ a b →
      cosPair h a b + j · sinPair h j a b ≡ a
    euler h j half square a b =
      cosPair h a b + j · sinPair h j a b
        ≡⟨ solve! R ⟩
      h · ((a + b) - (j · j) · (a - b))
        ≡⟨ cong (λ x → h · ((a + b) - x · (a - b))) square ⟩
      h · ((a + b) - (- 1r) · (a - b))
        ≡⟨ solve! R ⟩
      (h + h) · a
        ≡⟨ cong (_· a) half ⟩
      1r · a ≡⟨ ·IdL a ⟩ a ∎

    cosPair-mul : ∀ h j → h + h ≡ 1r → j · j ≡ - 1r → ∀ a b c d →
      cosPair h a b · cosPair h c d - sinPair h j a b · sinPair h j c d ≡
      cosPair h (a · c) (b · d)
    cosPair-mul h j half square a b c d =
      cosPair h a b · cosPair h c d - sinPair h j a b · sinPair h j c d
        ≡⟨ solve! R ⟩
      (h · h) · ((a + b) · (c + d) - (j · j) · ((a - b) · (c - d)))
        ≡⟨ cong (λ x → (h · h) · ((a + b) · (c + d) - x · ((a - b) · (c - d)))) square ⟩
      (h · h) · ((a + b) · (c + d) - (- 1r) · ((a - b) · (c - d)))
        ≡⟨ solve! R ⟩
      (h + h) · cosPair h (a · c) (b · d)
        ≡⟨ cong (_· cosPair h (a · c) (b · d)) half ⟩
      1r · cosPair h (a · c) (b · d)
        ≡⟨ ·IdL _ ⟩ cosPair h (a · c) (b · d) ∎

    sinPair-mul : ∀ h j → h + h ≡ 1r → ∀ a b c d →
      sinPair h j a b · cosPair h c d + cosPair h a b · sinPair h j c d ≡
      sinPair h j (a · c) (b · d)
    sinPair-mul h j half a b c d =
      sinPair h j a b · cosPair h c d + cosPair h a b · sinPair h j c d
        ≡⟨ solve! R ⟩
      (h + h) · sinPair h j (a · c) (b · d)
        ≡⟨ cong (_· sinPair h j (a · c) (b · d)) half ⟩
      1r · sinPair h j (a · c) (b · d)
        ≡⟨ ·IdL _ ⟩ sinPair h j (a · c) (b · d) ∎

    pythagorean-sign : ∀ a b → a · a - b · (- b) ≡ a · a + b · b
    pythagorean-sign a b = solve! R

module RealRestriction {ℓ} (R : CommRing ℓ) where
  open CommRingStr (snd R)
  open Cartesian.Cartesian R
  private module E = EulerAlgebra pairCommRing

  opaque
    cosPair-real : ∀ h → h + h ≡ 1r → ∀ c s →
      E.cosPair (embed h) (c , s) (c , - s) ≡ embed c
    cosPair-real h half c s = cong₂ _,_
      ((solve! R) ∙ cong (_· c) half ∙ ·IdL c) (solve! R)

    sinPair-real : ∀ h → h + h ≡ 1r → ∀ c s →
      E.sinPair (embed h) iℂ (c , s) (c , - s) ≡ embed s
    sinPair-real h half c s = cong₂ _,_
      ((solve! R) ∙ cong (_· s) half ∙ ·IdL s) (solve! R)
