module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Damped.Invariants where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Int.Fast using (pos)
open import Cubical.Data.NatPlusOne using (1+_)
open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Base using ([_/_]; eq/)
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.Scalar.Base
open import Cubical.Analysis.Real.Algebra.Scalar.Compatibility
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Bishop.CosineAtZero
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Damped.Iteration
  renaming (dampedBishopPiHalfApproximation to d)
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Damped.Bounds

opaque
  dampedBishopCoefficient-path : dampedBishopCoefficient ≡ [ pos 1 / 1+ 1 ]
  dampedBishopCoefficient-path = eq/ _ _ refl

  dampedBishopScalarPath : ∀ x → dampedBishopCoefficient ⋆ x ≡ damping · x
  dampedBishopScalarPath x = scalar-as-mul dampedBishopCoefficient x
    ∙ cong (λ z → rat z · x) dampedBishopCoefficient-path

private
  -- Transport the recurrence as a function of its step map. Pointwise
  -- scalar conversions at cos(d n) make the checker unfold entire series.
  scalarStep : ℝ → ℝ
  scalarStep x = x + dampedBishopCoefficient ⋆ cosℝ x

  opaque
    scalarStepPath : scalarStep ≡ step
    scalarStepPath = funExt λ x → cong (x +_) (dampedBishopScalarPath (cosℝ x))

    scalarRecurrence : ∀ n → d (suc n) ≡ scalarStep (d n)
    scalarRecurrence = dampedBishopPiHalfApproximation-step

opaque
  dampedBishopStep : ∀ n → d (suc n) ≡ step (d n)
  dampedBishopStep = subst (λ f → ∀ n → d (suc n) ≡ f (d n)) scalarStepPath scalarRecurrence

private
  opaque
    scalar-one : dampedBishopCoefficient ⋆ 1ℝ ≡ damping
    scalar-one = dampedBishopScalarPath 1ℝ ∙ mulIdR damping

opaque
  dampedBishopFirst : d 1 ≡ damping
  dampedBishopFirst = dampedBishopPiHalfApproximation-step zero
    ∙ cong₂ _+_ dampedBishopPiHalfApproximation-zero
        (cong (dampedBishopCoefficient ⋆_) (cong cosℝ dampedBishopPiHalfApproximation-zero))
    ∙ addIdL (dampedBishopCoefficient ⋆ cosℝ 0ℝ)
    ∙ cong (dampedBishopCoefficient ⋆_) bishopCosineAtZero
    ∙ scalar-one

-- Abstract the sequence while checking the induction. This prevents the
-- completed cosine values from being normalized through concrete iterates.
private
  module Recurrence (sequence : ℕ → ℝ)
    (start : sequence zero ≡ 0ℝ)
    (first : sequence 1 ≡ damping)
    (next : ∀ n → sequence (suc n) ≡ step (sequence n)) where

    opaque
      prefix : ∀ n → CosinePrefix (sequence n)
      prefix zero = subst CosinePrefix (sym start) initial-prefix
      prefix (suc n) = subst CosinePrefix (sym (next n))
        (step-prefix (sequence n) (prefix n))

    opaque
      increasing : ∀ n → sequence n ≤ℝ sequence (suc n)
      increasing n = subst (sequence n ≤ℝ_) (sym (next n))
        (step-increasing (sequence n) (fst (snd (prefix n))))

    opaque
      afterFirst : ∀ n → damping ≤ℝ sequence (suc n)
      afterFirst zero = subst (damping ≤ℝ_) (sym first) (≤ℝ-refl damping)
      afterFirst (suc n) = ≤ℝ-trans damping (sequence (suc n)) (sequence (suc (suc n)))
        (afterFirst n) (increasing (suc n))

  module IterationProperties = Recurrence d dampedBishopPiHalfApproximation-zero dampedBishopFirst dampedBishopStep

opaque
  dampedBishopPrefix : ∀ n → CosinePrefix (d n)
  dampedBishopPrefix = IterationProperties.prefix

  dampedBishopIncreasing : ∀ n → d n ≤ℝ d (suc n)
  dampedBishopIncreasing = IterationProperties.increasing

  dampedBishopAfterFirst : ∀ n → damping ≤ℝ d (suc n)
  dampedBishopAfterFirst = IterationProperties.afterFirst
