module Cubical.Analysis.Complex.Polynomial.BinomialAlgebra where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Vec using ([]; _∷_; replicate)
open import Cubical.Algebra.CommRing
import Cubical.Analysis.Complex.Polynomial.MonicAlgebra as MonicDefinition

module Binomial {ℓ} (R : CommRing ℓ) where
  open CommRingStr (snd R)
  open Exponentiation R
  open MonicDefinition.Monic R

  monomial : (n : ℕ) → MonicPolynomial n
  monomial n = replicate {n = n} 0r

  evaluate-monomial : ∀ n z → evaluateMonic (monomial n) z ≡ z ^ n
  evaluate-monomial zero z = refl
  evaluate-monomial (suc n) z = +IdL (z · evaluateMonic (monomial n) z)
    ∙ cong (z ·_) (evaluate-monomial n z)

  -- binomial n a represents X^(suc n) + a, including formal degree one.
  binomial : (n : ℕ) → fst R → MonicPolynomial (suc n)
  binomial n a = a ∷ monomial n

  evaluate-binomial : ∀ n a z → evaluateMonic (binomial n a) z ≡ a + z ^ suc n
  evaluate-binomial n a z = cong (λ w → a + z · w) (evaluate-monomial n z)
