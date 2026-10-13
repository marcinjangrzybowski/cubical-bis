module Cubical.Analysis.Complex.Polar.Algebra where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver
import Cubical.Analysis.Complex.Algebra.Cartesian as CartesianDefinition

module PolarAlgebra {ℓ} (R : CommRing ℓ) where
  open CommRingStr (snd R)
  open CartesianDefinition.Cartesian R

  otherSquare : ∀ a b c s → a · a + b · b ≡ 1r → s · s + c · c ≡ 1r → s ≡ b →
    c · c ≡ a · a
  otherSquare a b c s unit circle sine =
    c · c
      ≡⟨ solve! R ⟩
    (s · s + c · c) - s · s
      ≡⟨ cong₂ _-_ circle (cong (λ u → u · u) sine) ⟩
    1r - b · b
      ≡⟨ cong (_- b · b) (sym unit) ⟩
    (a · a + b · b) - b · b
      ≡⟨ solve! R ⟩
    a · a ∎

  normalizedSquare : ∀ a b r k → r · r ≡ a · a + b · b → r · k ≡ 1r →
    (a · k) · (a · k) + (b · k) · (b · k) ≡ 1r
  normalizedSquare a b r k square inverse =
    (a · k) · (a · k) + (b · k) · (b · k)
      ≡⟨ solve! R ⟩
    (a · a + b · b) · (k · k)
      ≡⟨ cong (_· (k · k)) (sym square) ⟩
    (r · r) · (k · k)
      ≡⟨ solve! R ⟩
    (r · k) · (r · k)
      ≡⟨ cong (λ u → u · u) inverse ⟩
    1r · 1r
      ≡⟨ ·IdR 1r ⟩
    1r ∎

  scaledCoordinates : ∀ r a b → embed r ·ℂ (a , b) ≡ (r · a , r · b)
  scaledCoordinates r a b = cong₂ _,_ (solve! R) (solve! R)

  undoScale : ∀ r k a b → r · k ≡ 1r → embed r ·ℂ (a · k , b · k) ≡ (a , b)
  undoScale r k a b inverse = scaledCoordinates r (a · k) (b · k)
    ∙ cong₂ _,_ (recover a) (recover b)
    where
    recover : ∀ x → r · (x · k) ≡ x
    recover x = (solve! R) ∙ cong (_· x) inverse ∙ (solve! R)

  quarterRotate : ∀ a b → iℂ ·ℂ (a , b) ≡ (- b , a)
  quarterRotate a b = cong₂ _,_ (solve! R) (solve! R)

  undoQuarterRotate : ∀ a b → iℂ ·ℂ (b , - a) ≡ (a , b)
  undoQuarterRotate a b = cong₂ _,_ (solve! R) (solve! R)

  negativeQuarterRotate : ∀ a b → (-ℂ iℂ) ·ℂ (a , b) ≡ (b , - a)
  negativeQuarterRotate a b = cong₂ _,_ (solve! R) (solve! R)
