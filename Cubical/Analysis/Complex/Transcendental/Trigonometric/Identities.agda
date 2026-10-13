module Cubical.Analysis.Complex.Transcendental.Trigonometric.Identities where

open import Cubical.Foundations.Prelude
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Transcendental.Exponential.Base
open import Cubical.Analysis.Complex.Transcendental.Trigonometric.Constants
open import Cubical.Analysis.Complex.Transcendental.Trigonometric.Base
import Cubical.Analysis.Complex.Transcendental.Trigonometric.Algebra as Algebra

private
  module E = Algebra.EulerAlgebra ℂCommRing

  exp-i-neg : ∀ z → expℂ (iℂ ·ℂ (-ℂ z)) ≡ expℂ (-ℂ (iℂ ·ℂ z))
  exp-i-neg z = cong expℂ (ℂRing.-DistR· iℂ z)

  exp-neg-i-neg : ∀ z → expℂ (-ℂ (iℂ ·ℂ (-ℂ z))) ≡ expℂ (iℂ ·ℂ z)
  exp-neg-i-neg z = cong expℂ
    (cong -ℂ_ (ℂRing.-DistR· iℂ z) ∙ ℂRing.-Idempotent (iℂ ·ℂ z))

  exp-i-add : ∀ z w → expℂ (iℂ ·ℂ (z +ℂ w)) ≡ expℂ (iℂ ·ℂ z) ·ℂ expℂ (iℂ ·ℂ w)
  exp-i-add z w = cong expℂ (·ℂDistR+ iℂ z w) ∙ expℂ-add (iℂ ·ℂ z) (iℂ ·ℂ w)

  exp-neg-i-add : ∀ z w → expℂ (-ℂ (iℂ ·ℂ (z +ℂ w))) ≡
    expℂ (-ℂ (iℂ ·ℂ z)) ·ℂ expℂ (-ℂ (iℂ ·ℂ w))
  exp-neg-i-add z w = cong expℂ
    (cong -ℂ_ (·ℂDistR+ iℂ z w) ∙ sym (ℂRing.-Dist (iℂ ·ℂ z) (iℂ ·ℂ w)))
    ∙ expℂ-add (-ℂ (iℂ ·ℂ z)) (-ℂ (iℂ ·ℂ w))

opaque
  unfolding cosℂ sinℂ

  cosℂ-neg : ∀ z → cosℂ (-ℂ z) ≡ cosℂ z
  cosℂ-neg z = cong₂ cosFromExp (exp-i-neg z) (exp-neg-i-neg z)
    ∙ E.cosPair-swap halfℂ (expℂ (iℂ ·ℂ z)) (expℂ (-ℂ (iℂ ·ℂ z)))

  sinℂ-neg : ∀ z → sinℂ (-ℂ z) ≡ -ℂ sinℂ z
  sinℂ-neg z = cong₂ sinFromExp (exp-i-neg z) (exp-neg-i-neg z)
    ∙ E.sinPair-swap halfℂ iℂ (expℂ (iℂ ·ℂ z)) (expℂ (-ℂ (iℂ ·ℂ z)))

  cosℂ-add : ∀ z w → cosℂ (z +ℂ w) ≡ cosℂ z ·ℂ cosℂ w -ℂ sinℂ z ·ℂ sinℂ w
  cosℂ-add z w = cong₂ cosFromExp (exp-i-add z w) (exp-neg-i-add z w)
    ∙ sym (E.cosPair-mul halfℂ iℂ halfℂ-double i²≡-1
      (expℂ (iℂ ·ℂ z)) (expℂ (-ℂ (iℂ ·ℂ z)))
      (expℂ (iℂ ·ℂ w)) (expℂ (-ℂ (iℂ ·ℂ w))))

  sinℂ-add : ∀ z w → sinℂ (z +ℂ w) ≡ sinℂ z ·ℂ cosℂ w +ℂ cosℂ z ·ℂ sinℂ w
  sinℂ-add z w = cong₂ sinFromExp (exp-i-add z w) (exp-neg-i-add z w)
    ∙ sym (E.sinPair-mul halfℂ iℂ halfℂ-double
      (expℂ (iℂ ·ℂ z)) (expℂ (-ℂ (iℂ ·ℂ z)))
      (expℂ (iℂ ·ℂ w)) (expℂ (-ℂ (iℂ ·ℂ w))))

opaque
  -- Algebraic squares, not squared complex moduli.
  cos²+sin²≡1ℂ : ∀ z → cosℂ z ·ℂ cosℂ z +ℂ sinℂ z ·ℂ sinℂ z ≡ 1ℂ
  cos²+sin²≡1ℂ z = sym
    (sym cosℂ-zero ∙ cong cosℂ (sym (+ℂInvR z)) ∙ cosℂ-add z (-ℂ z)
      ∙ cong₂ (λ c s → cosℂ z ·ℂ c -ℂ sinℂ z ·ℂ s) (cosℂ-neg z) (sinℂ-neg z)
      ∙ E.pythagorean-sign (cosℂ z) (sinℂ z))
