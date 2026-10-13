module Cubical.Analysis.Complex.Transcendental.Trigonometric.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Transcendental.Exponential.Base
open import Cubical.Analysis.Complex.Transcendental.Trigonometric.Constants
import Cubical.Analysis.Complex.Transcendental.Trigonometric.Algebra as Algebra

private module E = Algebra.EulerAlgebra ℂCommRing

cosFromExp : ℂ → ℂ → ℂ
cosFromExp = E.cosPair halfℂ

sinFromExp : ℂ → ℂ → ℂ
sinFromExp = E.sinPair halfℂ iℂ

-- The two exponentials exist everywhere. No division by a varying complex
-- number or choice of argument occurs. Derivative.agda proves entireness.
opaque
  cosℂ : ℂ → ℂ
  cosℂ z = cosFromExp (expℂ (iℂ ·ℂ z)) (expℂ (-ℂ (iℂ ·ℂ z)))

  sinℂ : ℂ → ℂ
  sinℂ z = sinFromExp (expℂ (iℂ ·ℂ z)) (expℂ (-ℂ (iℂ ·ℂ z)))

  cosℂ-exp : ∀ z → cosℂ z ≡ cosFromExp (expℂ (iℂ ·ℂ z)) (expℂ (-ℂ (iℂ ·ℂ z)))
  cosℂ-exp z = refl

  sinℂ-exp : ∀ z → sinℂ z ≡ sinFromExp (expℂ (iℂ ·ℂ z)) (expℂ (-ℂ (iℂ ·ℂ z)))
  sinℂ-exp z = refl

  cosℂ-zero : cosℂ 0ℂ ≡ 1ℂ
  cosℂ-zero = cong₂ cosFromExp
    (cong expℂ (ℂRing.0RightAnnihilates iℂ) ∙ expℂ-zero)
    (cong expℂ (cong -ℂ_ (ℂRing.0RightAnnihilates iℂ) ∙ ℂRing.0Selfinverse) ∙ expℂ-zero)
    ∙ E.cosPair-one halfℂ halfℂ-double

  sinℂ-zero : sinℂ 0ℂ ≡ 0ℂ
  sinℂ-zero = cong₂ sinFromExp
    (cong expℂ (ℂRing.0RightAnnihilates iℂ) ∙ expℂ-zero)
    (cong expℂ (cong -ℂ_ (ℂRing.0RightAnnihilates iℂ) ∙ ℂRing.0Selfinverse) ∙ expℂ-zero)
    ∙ E.sinPair-same halfℂ iℂ 1ℂ

  expℂ-euler-decomposition : ∀ z → expℂ (iℂ ·ℂ z) ≡ cosℂ z +ℂ iℂ ·ℂ sinℂ z
  expℂ-euler-decomposition z = sym
    (E.euler halfℂ iℂ halfℂ-double i²≡-1 (expℂ (iℂ ·ℂ z)) (expℂ (-ℂ (iℂ ·ℂ z))))
