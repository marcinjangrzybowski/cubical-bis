module Cubical.Analysis.Complex.Transcendental.Trigonometric.RealAxis where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.AdditiveGroup using (negZero)
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Conjugation
open import Cubical.Analysis.Complex.Polar.Cis
open import Cubical.Analysis.Complex.Transcendental.Exponential.Base
open import Cubical.Analysis.Complex.Transcendental.Trigonometric.Constants
open import Cubical.Analysis.Complex.Transcendental.Trigonometric.Base
import Cubical.Analysis.Complex.Transcendental.Trigonometric.Algebra as Algebra
import Cubical.Analysis.Complex.Polar.Algebra as PolarAlgebra

private
  module A = Algebra.RealRestriction ℝCommRing

  module P = PolarAlgebra.PolarAlgebra ℝCommRing

  imaginary-value : ∀ x → iℂ ·ℂ fromℝ x ≡ (0ℝ , x)
  imaginary-value x = P.quarterRotate x 0ℝ ∙ ℂ≡ negZero refl

  negate-imaginary : ∀ x → -ℂ (iℂ ·ℂ fromℝ x) ≡ conjugate (iℂ ·ℂ fromℝ x)
  negate-imaginary x = cong -ℂ_ (imaginary-value x)
    ∙ ℂ≡ negZero refl ∙ cong conjugate (sym (imaginary-value x))

  exp-negative-i-real : ∀ x → expℂ (-ℂ (iℂ ·ℂ fromℝ x)) ≡ conjugate (cisℝ x)
  exp-negative-i-real x = cong expℂ (negate-imaginary x)
    ∙ expℂ-conjugate (iℂ ·ℂ fromℝ x) ∙ cong conjugate (expℂ-euler x)

opaque
  cosℂ-fromℝ : ∀ x → cosℂ (fromℝ x) ≡ fromℝ (cosℝ x)
  cosℂ-fromℝ x = cosℂ-exp (fromℝ x)
    ∙ cong₂ cosFromExp (expℂ-euler x) (exp-negative-i-real x)
    ∙ cong (λ z → cosFromExp z (conjugate z)) (cisℝ-value x)
    ∙ A.cosPair-real halfℝ halfℝ-double (cosℝ x) (sinℝ x)

  sinℂ-fromℝ : ∀ x → sinℂ (fromℝ x) ≡ fromℝ (sinℝ x)
  sinℂ-fromℝ x = sinℂ-exp (fromℝ x)
    ∙ cong₂ sinFromExp (expℂ-euler x) (exp-negative-i-real x)
    ∙ cong (λ z → sinFromExp z (conjugate z)) (cisℝ-value x)
    ∙ A.sinPair-real halfℝ halfℝ-double (cosℝ x) (sinℝ x)

  expℂ-euler-real : ∀ x → expℂ (iℂ ·ℂ fromℝ x) ≡
    fromℝ (cosℝ x) +ℂ iℂ ·ℂ fromℝ (sinℝ x)
  expℂ-euler-real x = expℂ-euler-decomposition (fromℝ x)
    ∙ cong₂ (λ c s → c +ℂ iℂ ·ℂ s) (cosℂ-fromℝ x) (sinℂ-fromℝ x)
