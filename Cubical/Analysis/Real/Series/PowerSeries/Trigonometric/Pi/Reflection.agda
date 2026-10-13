module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Reflection where

open import Cubical.Foundations.Prelude
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AdditiveGroup.Properties
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Value

private
  opaque
    negativeShift : ∀ (f : ℝ → ℝ) p → (∀ x → f (x + p) ≡ f x) →
      ∀ x → f (x + (- p)) ≡ f x
    negativeShift f p period x = sym (period (x - p)) ∙ cong f (subAddCancel x p)

    negativeAntiShift : ∀ (f : ℝ → ℝ) p → (∀ x → f (x + p) ≡ - f x) →
      ∀ x → f (x + (- p)) ≡ - f x
    negativeAntiShift f p shift x = sym (negInvol (f (x + (- p))))
      ∙ cong -_ (sym (shift (x - p)) ∙ cong f (subAddCancel x p))

  opaque
    inversePhase : ∀ (f g : ℝ → ℝ) p → (∀ x → f (x + p) ≡ g x) →
      ∀ x → g (x + (- p)) ≡ f x
    inversePhase f g p phase x = sym (phase (x + (- p)))
      ∙ cong f (subAddCancel x p)

    inverseNegativePhase : ∀ (f g : ℝ → ℝ) p → (∀ x → f (x + p) ≡ - g x) →
      ∀ x → g (x + (- p)) ≡ - f x
    inverseNegativePhase f g p phase x = sym (negInvol (g (x + (- p))))
      ∙ cong -_ (sym (phase (x + (- p))) ∙ cong f (subAddCancel x p))

opaque
  sinℝ-sub-halfPiℝ : ∀ x → sinℝ (x + (- halfPiℝ)) ≡ - cosℝ x
  sinℝ-sub-halfPiℝ = inverseNegativePhase cosℝ sinℝ halfPiℝ cosℝ-add-halfPiℝ

  cosℝ-sub-halfPiℝ : ∀ x → cosℝ (x + (- halfPiℝ)) ≡ sinℝ x
  cosℝ-sub-halfPiℝ = inversePhase sinℝ cosℝ halfPiℝ sinℝ-add-halfPiℝ

  cosℝ≡neg-sinℝ-sub-halfPiℝ : ∀ x → cosℝ x ≡ - sinℝ (x + (- halfPiℝ))
  cosℝ≡neg-sinℝ-sub-halfPiℝ x = sym
    (cong -_ (sinℝ-sub-halfPiℝ x) ∙ negInvol (cosℝ x))

  sinℝ-halfPiℝ-sub : ∀ x → sinℝ (halfPiℝ + (- x)) ≡ cosℝ x
  sinℝ-halfPiℝ-sub x = cong sinℝ (addComm halfPiℝ (- x))
    ∙ sinℝ-add-halfPiℝ (- x) ∙ cosℝ-neg x

  cosℝ-halfPiℝ-sub : ∀ x → cosℝ (halfPiℝ + (- x)) ≡ sinℝ x
  cosℝ-halfPiℝ-sub x = cong cosℝ (addComm halfPiℝ (- x))
    ∙ cosℝ-add-halfPiℝ (- x) ∙ cong -_ (sinℝ-neg x) ∙ negInvol (sinℝ x)

  sinℝ-sub-piℝ : ∀ x → sinℝ (x + (- piℝ)) ≡ - sinℝ x
  sinℝ-sub-piℝ = negativeAntiShift sinℝ piℝ sinℝ-add-piℝ

  cosℝ-sub-piℝ : ∀ x → cosℝ (x + (- piℝ)) ≡ - cosℝ x
  cosℝ-sub-piℝ = negativeAntiShift cosℝ piℝ cosℝ-add-piℝ

  sinℝ-piℝ-sub : ∀ x → sinℝ (piℝ + (- x)) ≡ sinℝ x
  sinℝ-piℝ-sub x = cong sinℝ (addComm piℝ (- x))
    ∙ sinℝ-add-piℝ (- x) ∙ cong -_ (sinℝ-neg x) ∙ negInvol (sinℝ x)

  cosℝ-piℝ-sub : ∀ x → cosℝ (piℝ + (- x)) ≡ - cosℝ x
  cosℝ-piℝ-sub x = cong cosℝ (addComm piℝ (- x))
    ∙ cosℝ-add-piℝ (- x) ∙ cong -_ (cosℝ-neg x)

  sinℝ-sub-twoPiℝ : ∀ x → sinℝ (x + (- twoPiℝ)) ≡ sinℝ x
  sinℝ-sub-twoPiℝ = negativeShift sinℝ twoPiℝ sinℝ-periodic

  cosℝ-sub-twoPiℝ : ∀ x → cosℝ (x + (- twoPiℝ)) ≡ cosℝ x
  cosℝ-sub-twoPiℝ = negativeShift cosℝ twoPiℝ cosℝ-periodic

  sinℝ-twoPiℝ-sub : ∀ x → sinℝ (twoPiℝ + (- x)) ≡ - sinℝ x
  sinℝ-twoPiℝ-sub x = cong sinℝ (addComm twoPiℝ (- x))
    ∙ sinℝ-periodic (- x) ∙ sinℝ-neg x

  cosℝ-twoPiℝ-sub : ∀ x → cosℝ (twoPiℝ + (- x)) ≡ cosℝ x
  cosℝ-twoPiℝ-sub x = cong cosℝ (addComm twoPiℝ (- x))
    ∙ cosℝ-periodic (- x) ∙ cosℝ-neg x
