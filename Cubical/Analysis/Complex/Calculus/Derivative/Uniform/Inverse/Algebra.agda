module Cubical.Analysis.Complex.Calculus.Derivative.Uniform.Inverse.Algebra where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
import Cubical.Algebra.Ring.Properties as RingProperties
import Cubical.Analysis.Complex.Algebra.Identities as Algebra
import Cubical.Analysis.Complex.Polynomial.Newton.Algebra as Newton

module InverseRemainder {ℓ} (R : CommRing ℓ) where
  open CommRingStr (snd R)
  private
    module Ring = RingProperties.RingTheory (CommRing→Ring R)
    module A = Algebra.Identities R
    module N = Newton.NewtonIdentities R

  opaque
    inverseError : ∀ inverse derivative → inverse · derivative ≡ 1r → ∀ x y u v →
      (v - u) - inverse · (y - x) ≡ (- inverse) · ((y - x) - derivative · (v - u))
    inverseError inverse derivative law x y u v =
      sym (A.sumDifference v (- (inverse · y)) u (- (inverse · x))
        ∙ cong ((v - u) +_) (A.negativeDifference (inverse · y) (inverse · x))
        ∙ cong (λ k → (v - u) - k) (sym (Ring.·DistR- inverse y x)))
      ∙ N.difference inverse derivative law v u y x

