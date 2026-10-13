module Cubical.Analysis.Complex.Transcendental.HigherDerivative where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Calculus.Derivative.Base
open import Cubical.Analysis.Complex.Calculus.Derivative.Algebra
open import Cubical.Analysis.Complex.Calculus.Derivative.Tower
open import Cubical.Analysis.Complex.Transcendental.Exponential.Base
open import Cubical.Analysis.Complex.Transcendental.Exponential.Derivative
open import Cubical.Analysis.Complex.Transcendental.Trigonometric.Base
open import Cubical.Analysis.Complex.Transcendental.Trigonometric.Derivative

exponentialDerivativeTower : IsComplexDerivativeTower (λ _ → expℂ)
exponentialDerivativeTower _ = expℂHasSelfDerivative

-- Full complex derivatives, with the familiar four-cycle encoded by the
-- successor recurrences rather than a second modular-arithmetic convention.
mutual
  sineDerivativeℂ : ℕ → ℂ → ℂ
  sineDerivativeℂ zero = sinℂ
  sineDerivativeℂ (suc n) = cosineDerivativeℂ n

  cosineDerivativeℂ : ℕ → ℂ → ℂ
  cosineDerivativeℂ zero = cosℂ
  cosineDerivativeℂ (suc n) z = -ℂ sineDerivativeℂ n z

mutual
  sineDerivativeTower : IsComplexDerivativeTower sineDerivativeℂ
  sineDerivativeTower zero = sinℂHasDerivative
  sineDerivativeTower (suc n) = cosineDerivativeTower n

  cosineDerivativeTower : IsComplexDerivativeTower cosineDerivativeℂ
  cosineDerivativeTower zero = cosℂHasDerivative
  cosineDerivativeTower (suc n) = negHasComplexDerivative (sineDerivativeℂ n) (sineDerivativeℂ (suc n)) (sineDerivativeTower n)

sineDerivativeℂ-two : ∀ n z → sineDerivativeℂ (suc (suc n)) z ≡ -ℂ sineDerivativeℂ n z
sineDerivativeℂ-two n z = refl

cosineDerivativeℂ-two : ∀ n z → cosineDerivativeℂ (suc (suc n)) z ≡ -ℂ cosineDerivativeℂ n z
cosineDerivativeℂ-two n z = refl

sineDerivativeℂ-four : ∀ n z → sineDerivativeℂ (suc (suc (suc (suc n)))) z ≡ sineDerivativeℂ n z
sineDerivativeℂ-four n z = ℂRing.-Idempotent (sineDerivativeℂ n z)

cosineDerivativeℂ-four : ∀ n z → cosineDerivativeℂ (suc (suc (suc (suc n)))) z ≡ cosineDerivativeℂ n z
cosineDerivativeℂ-four n z = ℂRing.-Idempotent (cosineDerivativeℂ n z)
