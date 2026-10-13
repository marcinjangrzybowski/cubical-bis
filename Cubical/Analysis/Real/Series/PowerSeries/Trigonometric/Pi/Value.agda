module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Value where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Algebra.CommRing
import Cubical.Algebra.Ring.Properties as RingProperties
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AdditiveGroup.Properties
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ)
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Real.Order.Strict.Located
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Phase
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.AbsoluteCosine
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Characterization
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Definition
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Orientation
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.QuarterTurn
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Damped.Characterization

private
  module R = RingProperties.RingTheory (CommRing→Ring ℝCommRing)

-- These are native Analysis reals, constructed without a supplied Cauchy,
-- intermediate-value, inverse-trigonometric, or choice witness.
halfPiℝ : ℝ
halfPiℝ = characterizedHalfPi dampedBishopHalfPi

piℝ : ℝ
piℝ = halfPiℝ + halfPiℝ

twoPiℝ : ℝ
twoPiℝ = piℝ + piℝ

opaque
  halfPiℝ-characterization : IsFirstPositiveCosineZero halfPiℝ
  halfPiℝ-characterization = subst {x = fst dampedBishopHalfPi} {y = halfPiℝ}
    IsFirstPositiveCosineZero refl (snd dampedBishopHalfPi)

  halfPiℝ-positive : 0ℝ <ℝ halfPiℝ
  halfPiℝ-positive = firstPositiveCosineZero-positive {half = halfPiℝ} halfPiℝ-characterization

  cosℝ-halfPiℝ : cosℝ halfPiℝ ≡ 0ℝ
  cosℝ-halfPiℝ = firstPositiveCosineZero-zero {half = halfPiℝ} halfPiℝ-characterization

  cosℝ-positive-before-halfPiℝ : ∀ x → 0ℝ ≤ℝ x → x <ℝ halfPiℝ → 0ℝ <ℝ cosℝ x
  cosℝ-positive-before-halfPiℝ = firstPositiveCosineZero-positive-before {half = halfPiℝ} halfPiℝ-characterization

  halfPiℝ-leastNonnegativeCosineZero : IsLeastNonnegativeCosineZero halfPiℝ
  halfPiℝ-leastNonnegativeCosineZero = firstPositiveCosineZero→leastNonnegativeCosineZero {half = halfPiℝ} halfPiℝ-characterization

  halfPiℝ-unique : ∀ x → IsFirstPositiveCosineZero x → x ≡ halfPiℝ
  halfPiℝ-unique x p = firstPositiveCosineZero-unique {left = x} {right = halfPiℝ} p halfPiℝ-characterization

  sinℝ-halfPiℝ : sinℝ halfPiℝ ≡ 1ℝ
  sinℝ-halfPiℝ = subst {x = fst dampedBishopHalfPi} {y = halfPiℝ}
    (λ z → sinℝ z ≡ 1ℝ) refl (characterizedHalfPi-sineOne dampedBishopHalfPi)

  halfPiℝ-quarterTurn : IsPositiveQuarterTurn halfPiℝ
  halfPiℝ-quarterTurn = cosℝ-halfPiℝ , sinℝ-halfPiℝ

  piℝ-positive : 0ℝ <ℝ piℝ
  piℝ-positive = subst (_<ℝ piℝ) (addIdL 0ℝ)
    (<ℝ-add 0ℝ halfPiℝ 0ℝ halfPiℝ halfPiℝ-positive halfPiℝ-positive)

  sinℝ-piℝ : sinℝ piℝ ≡ 0ℝ
  sinℝ-piℝ = subst {x = characterizedPi dampedBishopHalfPi} {y = piℝ}
    (λ z → sinℝ z ≡ 0ℝ) refl
    (sinℝ-characterizedPi dampedBishopHalfPi (characterizedHalfPi-sineOne dampedBishopHalfPi))

  cosℝ-piℝ : cosℝ piℝ ≡ - 1ℝ
  cosℝ-piℝ = subst {x = characterizedPi dampedBishopHalfPi} {y = piℝ}
    (λ z → cosℝ z ≡ - 1ℝ) refl
    (cosℝ-characterizedPi dampedBishopHalfPi (characterizedHalfPi-sineOne dampedBishopHalfPi))

  sinℝ-add-halfPiℝ : ∀ x → sinℝ (x + halfPiℝ) ≡ cosℝ x
  sinℝ-add-halfPiℝ = sinℝ-add-quarterTurn halfPiℝ halfPiℝ-quarterTurn

  cosℝ-add-halfPiℝ : ∀ x → cosℝ (x + halfPiℝ) ≡ - sinℝ x
  cosℝ-add-halfPiℝ = cosℝ-add-quarterTurn halfPiℝ halfPiℝ-quarterTurn

  sinℝ-add-piℝ : ∀ x → sinℝ (x + piℝ) ≡ - sinℝ x
  sinℝ-add-piℝ = subst {x = characterizedPi dampedBishopHalfPi} {y = piℝ}
    (λ z → ∀ x → sinℝ (x + z) ≡ - sinℝ x) refl
    (sinℝ-add-characterizedPi dampedBishopHalfPi (characterizedHalfPi-sineOne dampedBishopHalfPi))

  cosℝ-add-piℝ : ∀ x → cosℝ (x + piℝ) ≡ - cosℝ x
  cosℝ-add-piℝ = subst {x = characterizedPi dampedBishopHalfPi} {y = piℝ}
    (λ z → ∀ x → cosℝ (x + z) ≡ - cosℝ x) refl
    (cosℝ-add-characterizedPi dampedBishopHalfPi (characterizedHalfPi-sineOne dampedBishopHalfPi))

  sinℝ-periodic : ∀ x → sinℝ (x + twoPiℝ) ≡ sinℝ x
  sinℝ-periodic = subst {x = characterizedTwoPi dampedBishopHalfPi} {y = twoPiℝ}
    (λ z → ∀ x → sinℝ (x + z) ≡ sinℝ x) refl
    (sinℝ-add-characterizedTwoPi dampedBishopHalfPi (characterizedHalfPi-sineOne dampedBishopHalfPi))

  cosℝ-periodic : ∀ x → cosℝ (x + twoPiℝ) ≡ cosℝ x
  cosℝ-periodic = subst {x = characterizedTwoPi dampedBishopHalfPi} {y = twoPiℝ}
    (λ z → ∀ x → cosℝ (x + z) ≡ cosℝ x) refl
    (cosℝ-add-characterizedTwoPi dampedBishopHalfPi (characterizedHalfPi-sineOne dampedBishopHalfPi))

  twoPiℝ-positive : 0ℝ <ℝ twoPiℝ
  twoPiℝ-positive = subst (_<ℝ twoPiℝ) (addIdL 0ℝ)
    (<ℝ-add 0ℝ piℝ 0ℝ piℝ piℝ-positive piℝ-positive)

  sinℝ-twoPiℝ : sinℝ twoPiℝ ≡ 0ℝ
  sinℝ-twoPiℝ = cong sinℝ (sym (addIdL twoPiℝ)) ∙ sinℝ-periodic 0ℝ ∙ sinℝ-zero

  cosℝ-twoPiℝ : cosℝ twoPiℝ ≡ 1ℝ
  cosℝ-twoPiℝ = cong cosℝ (sym (addIdL twoPiℝ)) ∙ cosℝ-periodic 0ℝ ∙ cosℝ-zero

  sinℝ-positive-before-piℝ : ∀ x → 0ℝ <ℝ x → x <ℝ piℝ → 0ℝ <ℝ sinℝ x
  sinℝ-positive-before-piℝ x positive below =
    subst (0ℝ <ℝ_)
      (sym (sinℝ-add-halfPiℝ (x - halfPiℝ)) ∙ cong sinℝ (subAddCancel x halfPiℝ))
      (characterizedCosine-positive-inside halfPiℝ halfPiℝ-characterization (x - halfPiℝ)
        (subst (_<ℝ x - halfPiℝ) (addIdL (- halfPiℝ)) (<ℝ-addR 0ℝ x (- halfPiℝ) positive))
        (subst (x - halfPiℝ <ℝ_) (R.plusMinus halfPiℝ halfPiℝ)
          (<ℝ-addR x piℝ (- halfPiℝ) below)))

  piℝ-characterization : (0ℝ <ℝ piℝ) × (sinℝ piℝ ≡ 0ℝ) ×
    (∀ x → 0ℝ <ℝ x → x <ℝ piℝ → 0ℝ <ℝ sinℝ x)
  piℝ-characterization = piℝ-positive , sinℝ-piℝ , sinℝ-positive-before-piℝ

  piℝ-leastPositiveSineZero : ∀ x → 0ℝ <ℝ x → sinℝ x ≡ 0ℝ → piℝ ≤ℝ x
  piℝ-leastPositiveSineZero x positive zero = notGreater→≤ℝ piℝ x λ below →
    <ℝ-irrefl 0ℝ (subst (0ℝ <ℝ_) zero (sinℝ-positive-before-piℝ x positive below))

  piℝ-unique : ∀ p → 0ℝ <ℝ p → sinℝ p ≡ 0ℝ →
    (∀ x → 0ℝ <ℝ x → x <ℝ p → 0ℝ <ℝ sinℝ x) → p ≡ piℝ
  piℝ-unique p positive zero before = ≤ℝ-antisym p piℝ
    (notGreater→≤ℝ p piℝ λ below →
      <ℝ-irrefl 0ℝ (subst (0ℝ <ℝ_) sinℝ-piℝ (before piℝ piℝ-positive below)))
    (piℝ-leastPositiveSineZero p positive zero)
