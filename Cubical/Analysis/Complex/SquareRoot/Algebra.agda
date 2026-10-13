module Cubical.Analysis.Complex.SquareRoot.Algebra where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver

module SquareRootAlgebra {ℓ} (R : CommRing ℓ) where
  open CommRingStr (snd R)

  private
    numerator : ∀ a b r h → h + h ≡ 1r → r · r ≡ a · a + b · b →
      ((r + a) · h) · ((r + a) · h) - (h · b) · (h · b) ≡ a · ((r + a) · h)
    numerator a b r h halves square =
      ((r + a) · h) · ((r + a) · h) - (h · b) · (h · b)
        ≡⟨ solve! R ⟩
      (h · h) · (r · r - (a · a + b · b)) + (h + h) · a · ((r + a) · h)
        ≡⟨ cong₂ (λ s u → (h · h) · (s - (a · a + b · b)) + u · a · ((r + a) · h)) square halves ⟩
      (h · h) · ((a · a + b · b) - (a · a + b · b)) + 1r · a · ((r + a) · h)
        ≡⟨ solve! R ⟩
      a · ((r + a) · h) ∎

  sqrtRealPart : ∀ a b r h t k → h + h ≡ 1r → r · r ≡ a · a + b · b →
    t · t ≡ (r + a) · h → t · k ≡ 1r →
    t · t - ((h · b) · k) · ((h · b) · k) ≡ a
  sqrtRealPart a b r h t k halves radius square inverse =
    t · t - ((h · b) · k) · ((h · b) · k)
      ≡⟨ solve! R ⟩
    (1r · 1r) · (t · t) - ((h · b) · k) · ((h · b) · k)
      ≡⟨ cong (λ u → (u · u) · (t · t) - ((h · b) · k) · ((h · b) · k)) (sym inverse) ⟩
    ((t · k) · (t · k)) · (t · t) - ((h · b) · k) · ((h · b) · k)
      ≡⟨ solve! R ⟩
    (k · k) · ((t · t) · (t · t) - (h · b) · (h · b))
      ≡⟨ cong (λ u → (k · k) · (u · u - (h · b) · (h · b))) square ⟩
    (k · k) · (((r + a) · h) · ((r + a) · h) - (h · b) · (h · b))
      ≡⟨ cong ((k · k) ·_) (numerator a b r h halves radius) ⟩
    (k · k) · (a · ((r + a) · h))
      ≡⟨ cong (λ u → (k · k) · (a · u)) (sym square) ⟩
    (k · k) · (a · (t · t))
      ≡⟨ solve! R ⟩
    a · ((t · k) · (t · k))
      ≡⟨ cong (λ u → a · (u · u)) inverse ⟩
    a · (1r · 1r)
      ≡⟨ solve! R ⟩
    a ∎

  sqrtImaginaryPart : ∀ b h t k → h + h ≡ 1r → t · k ≡ 1r →
    t · ((h · b) · k) + ((h · b) · k) · t ≡ b
  sqrtImaginaryPart b h t k halves inverse =
    t · ((h · b) · k) + ((h · b) · k) · t
      ≡⟨ solve! R ⟩
    (h + h) · b · (t · k)
      ≡⟨ cong₂ (λ u v → u · b · v) halves inverse ⟩
    1r · b · 1r
      ≡⟨ solve! R ⟩
    b ∎

  productSquare : ∀ z w → (z · w) · (z · w) ≡ (z · z) · (w · w)
  productSquare z w = solve! R
