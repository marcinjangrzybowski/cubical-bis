module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Integrals where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.AdditiveGroup.Properties
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Calculus.MeanValue.Uniform
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Base
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Laws.Neg
open import Cubical.Analysis.Real.Integration.RiemannIntegral.Extensionality
open import Cubical.Analysis.Real.Integration.FundamentalTheorem.Second
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Estimates.UniformDerivative

private
  opaque
    integrateNegativeDerivative : ∀ F f →
      IsRadiuswiseUniformDerivative F (λ x → - f x) →
      ∀ a b → HasRiemannIntegralOn f a b (F a - F b)
    integrateNegativeDerivative F f derivative a b =
      subst (HasRiemannIntegralOn f a b) (negSub (F b) (F a))
        (hasRiemannIntegral-congOn (λ x → - (- f x)) f a b
          (- (F b - F a)) (λ x _ _ → negInvol (f x))
          (negHasRiemannIntegral (λ x → - f x) (F b - F a)
            (fundamentalTheoremOfCalculusSecond F (λ x → - f x) a b
              (radiuswiseUniformDerivative→onInterval F (λ x → - f x)
                a b derivative))))

-- FTC constructs the integrals directly from the uniform derivatives.
-- No independent integrability or chosen continuity modulus is required.
opaque
  sinℝ-hasRiemannIntegral : ∀ a b →
    HasRiemannIntegralOn sinℝ a b (cosℝ a - cosℝ b)
  sinℝ-hasRiemannIntegral =
    integrateNegativeDerivative cosℝ sinℝ cosℝHasUniformDerivative

  cosℝ-hasRiemannIntegral : ∀ a b →
    HasRiemannIntegralOn cosℝ a b (sinℝ b - sinℝ a)
  cosℝ-hasRiemannIntegral a b =
    fundamentalTheoremOfCalculusSecond sinℝ cosℝ a b
      (radiuswiseUniformDerivative→onInterval sinℝ cosℝ a b sinℝHasUniformDerivative)

sinℝ-isRiemannIntegrable : ∀ a b → IsRiemannIntegrableOn sinℝ a b
sinℝ-isRiemannIntegrable a b = (cosℝ a - cosℝ b) , sinℝ-hasRiemannIntegral a b

cosℝ-isRiemannIntegrable : ∀ a b → IsRiemannIntegrableOn cosℝ a b
cosℝ-isRiemannIntegrable a b = (sinℝ b - sinℝ a) , cosℝ-hasRiemannIntegral a b

opaque
  integral-sinℝ : ∀ a b → a ≤ℝ b →
    (integrable : IsRiemannIntegrableOn sinℝ a b) →
    integral {f = sinℝ} {a = a} {b = b} integrable ≡ cosℝ a - cosℝ b
  integral-sinℝ a b a≤b integrable =
    riemannIntegralUnique a b a≤b sinℝ (fst integrable) (cosℝ a - cosℝ b)
      (snd integrable) (sinℝ-hasRiemannIntegral a b)

  integral-cosℝ : ∀ a b → a ≤ℝ b →
    (integrable : IsRiemannIntegrableOn cosℝ a b) →
    integral {f = cosℝ} {a = a} {b = b} integrable ≡ sinℝ b - sinℝ a
  integral-cosℝ a b a≤b integrable =
    riemannIntegralUnique a b a≤b cosℝ (fst integrable) (sinℝ b - sinℝ a)
      (snd integrable) (cosℝ-hasRiemannIntegral a b)
