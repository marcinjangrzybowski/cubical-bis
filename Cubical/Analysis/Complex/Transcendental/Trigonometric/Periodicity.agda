module Cubical.Analysis.Complex.Transcendental.Trigonometric.Periodicity where

open import Cubical.Foundations.Prelude
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Value
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Transcendental.Trigonometric.Base
open import Cubical.Analysis.Complex.Transcendental.Trigonometric.Identities
open import Cubical.Analysis.Complex.Transcendental.Trigonometric.RealAxis

opaque
  sinℂ-halfPi : sinℂ (fromℝ halfPiℝ) ≡ 1ℂ
  sinℂ-halfPi = sinℂ-fromℝ halfPiℝ ∙ cong fromℝ sinℝ-halfPiℝ

  cosℂ-halfPi : cosℂ (fromℝ halfPiℝ) ≡ 0ℂ
  cosℂ-halfPi = cosℂ-fromℝ halfPiℝ ∙ cong fromℝ cosℝ-halfPiℝ

  sinℂ-twoPi : sinℂ (fromℝ twoPiℝ) ≡ 0ℂ
  sinℂ-twoPi = sinℂ-fromℝ twoPiℝ ∙ cong fromℝ sinℝ-twoPiℝ

  cosℂ-twoPi : cosℂ (fromℝ twoPiℝ) ≡ 1ℂ
  cosℂ-twoPi = cosℂ-fromℝ twoPiℝ ∙ cong fromℝ cosℝ-twoPiℝ

  -- The period is real; this is distinct from the exponential's imaginary period.
  cosℂ-periodic : ∀ z → cosℂ (z +ℂ fromℝ twoPiℝ) ≡ cosℂ z
  cosℂ-periodic z = cosℂ-add z (fromℝ twoPiℝ)
    ∙ cong₂ (λ c s → cosℂ z ·ℂ c -ℂ sinℂ z ·ℂ s) cosℂ-twoPi sinℂ-twoPi
    ∙ cong₂ _-ℂ_ (·ℂIdR (cosℂ z)) (ℂRing.0RightAnnihilates (sinℂ z))
    ∙ cong (cosℂ z +ℂ_) ℂRing.0Selfinverse ∙ +ℂIdR (cosℂ z)

  sinℂ-periodic : ∀ z → sinℂ (z +ℂ fromℝ twoPiℝ) ≡ sinℂ z
  sinℂ-periodic z = sinℂ-add z (fromℝ twoPiℝ)
    ∙ cong₂ (λ c s → sinℂ z ·ℂ c +ℂ cosℂ z ·ℂ s) cosℂ-twoPi sinℂ-twoPi
    ∙ cong₂ _+ℂ_ (·ℂIdR (sinℂ z)) (ℂRing.0RightAnnihilates (cosℂ z))
    ∙ +ℂIdR (sinℂ z)
