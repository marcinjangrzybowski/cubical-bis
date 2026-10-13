module Cubical.Analysis.Complex.Polar.Cis.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Value
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Conjugation
open import Cubical.Analysis.Complex.Polar.Cis

opaque
  unfolding cisℝ

  cisℝ-neg : ∀ θ → cisℝ (- θ) ≡ conjugate (cisℝ θ)
  cisℝ-neg θ = ℂ≡ (cosℝ-neg θ) (sinℝ-neg θ)

  cisℝ-periodic : ∀ θ → cisℝ (θ + twoPiℝ) ≡ cisℝ θ
  cisℝ-periodic θ = ℂ≡ (cosℝ-periodic θ) (sinℝ-periodic θ)
