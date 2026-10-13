module Cubical.Analysis.Complex.Transcendental.Exponential.Derivative.Algebra where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver
import Cubical.Analysis.Complex.Algebra.Cartesian as Cartesian

-- The Cauchy--Riemann cancellation for e(x)(c(y) + i s(y)), assuming
-- e' = e, c' = -s and s' = c. Analytic bounds are supplied separately.
module SeparatedAlgebra {ℓ} (R : CommRing ℓ) where
  open CommRingStr (snd R)
  open Cartesian.Cartesian R

  opaque
    remainder : ∀ e₀ e₁ c₀ c₁ s₀ s₁ x₀ x₁ y₀ y₁ →
      ((embed e₁ ·ℂ (c₁ , s₁)) -ℂ (embed e₀ ·ℂ (c₀ , s₀))) -ℂ
        (embed e₀ ·ℂ (c₀ , s₀)) ·ℂ ((x₁ , y₁) -ℂ (x₀ , y₀)) ≡
      ((c₁ , s₁) ·ℂ embed ((e₁ - e₀) - e₀ · (x₁ - x₀)) +ℂ
        embed e₀ ·ℂ (embed ((c₁ - c₀) - (- s₀) · (y₁ - y₀)) +ℂ
          iℂ ·ℂ embed ((s₁ - s₀) - c₀ · (y₁ - y₀)))) +ℂ
      embed e₀ ·ℂ (((c₁ , s₁) -ℂ (c₀ , s₀)) ·ℂ embed (x₁ - x₀))
    remainder e₀ e₁ c₀ c₁ s₀ s₁ x₀ x₁ y₀ y₁ = cong₂ _,_ (solve! R) (solve! R)
