module Cubical.Analysis.Complex.Transcendental.HigherDerivative.Addition where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (zero; suc)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Transcendental.Trigonometric.Base
open import Cubical.Analysis.Complex.Transcendental.Trigonometric.Identities
open import Cubical.Analysis.Complex.Transcendental.HigherDerivative

-- Addition formulas for every actual complex derivative, proved from the
-- established first-order addition laws and the coherent successor cycle.
mutual
  sineDerivativeℂ-add : ∀ n z w → sineDerivativeℂ n (z +ℂ w) ≡
    sineDerivativeℂ n z ·ℂ cosℂ w +ℂ cosineDerivativeℂ n z ·ℂ sinℂ w
  sineDerivativeℂ-add zero z w = sinℂ-add z w
  sineDerivativeℂ-add (suc n) z w = cosineDerivativeℂ-add n z w
    ∙ cong (cosineDerivativeℂ n z ·ℂ cosℂ w +ℂ_)
        (sym (ℂRing.-DistL· (sineDerivativeℂ n z) (sinℂ w)))

  cosineDerivativeℂ-add : ∀ n z w → cosineDerivativeℂ n (z +ℂ w) ≡
    cosineDerivativeℂ n z ·ℂ cosℂ w -ℂ sineDerivativeℂ n z ·ℂ sinℂ w
  cosineDerivativeℂ-add zero z w = cosℂ-add z w
  cosineDerivativeℂ-add (suc n) z w = cong -ℂ_ (sineDerivativeℂ-add n z w)
    ∙ sym (ℂRing.-Dist (sineDerivativeℂ n z ·ℂ cosℂ w) (cosineDerivativeℂ n z ·ℂ sinℂ w))
    ∙ cong (_-ℂ cosineDerivativeℂ n z ·ℂ sinℂ w)
        (sym (ℂRing.-DistL· (sineDerivativeℂ n z) (cosℂ w)))
