module Cubical.Analysis.Complex.Polar.CoordinateCases where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sum as Sum
open import Cubical.Data.Empty as Empty
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Lattice
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Located
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Modulus.Base
open import Cubical.Analysis.Complex.Modulus.Bounds

private
  positiveAbsoluteCases : ∀ x → 0ℝ <ℝ absℝ x → ∥ (0ℝ <ℝ x) ⊎ (0ℝ <ℝ (- x)) ∥₁
  positiveAbsoluteCases x positive = PT.rec squash₁ first
    (dichotomyℝ 0ℝ x (absℝ x) positive)
    where
    first : (x <ℝ absℝ x) ⊎ (0ℝ <ℝ x) → ∥ (0ℝ <ℝ x) ⊎ (0ℝ <ℝ (- x)) ∥₁
    first (inr pos) = ∣ inl pos ∣₁
    first (inl smaller) = PT.map (Sum.rec impossible inr)
      (dichotomyℝ 0ℝ (- x) (absℝ x) positive)
      where
      impossible : (- x) <ℝ absℝ x → (0ℝ <ℝ x) ⊎ (0ℝ <ℝ (- x))
      impossible negative-smaller = Empty.rec (<ℝ-irrefl (absℝ x)
        (subst (_<ℝ absℝ x) (sym (absAsMax x))
          (maxStrictUpper x (- x) (absℝ x) smaller negative-smaller)))

CoordinateSigns : ℂ → Type₀
CoordinateSigns z = (0ℝ <ℝ re z) ⊎ ((0ℝ <ℝ (- re z)) ⊎
  ((0ℝ <ℝ im z) ⊎ (0ℝ <ℝ (- im z))))

-- Four open half-planes cover the apart-from-zero complex plane. This is a
-- finite truncated cover, not a decision of coordinate signs at zero.
nonzeroCoordinateCases : ∀ z → 0ℝ <ℝ modulusℂ z → ∥ CoordinateSigns z ∥₁
nonzeroCoordinateCases z positive = PT.rec squash₁ (Sum.rec real imaginary)
  (positiveSum→positiveSummand (absℝ (re z)) (absℝ (im z))
    (<≤ℝ-trans 0ℝ (modulusℂ z) (normℂ z) positive (modulusℂ≤normℂ z)))
  where
  real : 0ℝ <ℝ absℝ (re z) → ∥ CoordinateSigns z ∥₁
  real p = PT.map (Sum.rec inl (λ q → inr (inl q))) (positiveAbsoluteCases (re z) p)

  imaginary : 0ℝ <ℝ absℝ (im z) → ∥ CoordinateSigns z ∥₁
  imaginary p = PT.map (λ q → inr (inr q)) (positiveAbsoluteCases (im z) p)
