module Cubical.Analysis.Complex.Polynomial.Differential.Monic where

open import Cubical.Foundations.Prelude
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Polynomial.Base
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.Polynomial.Differential
import Cubical.Analysis.Complex.Polynomial.Differential.MonicAlgebra as MonicDifferentialDefinition

private module D = MonicDifferentialDefinition.MonicDifferential ℂCommRing

open D public using (monicCoefficients; derivativeMonic;
  derivative-addConstant; derivative-multiplyLinear; derivative-atRoot)

opaque
  unfolding evaluatePolynomialℂ polynomialDerivativeℂ

  evaluatePolynomialℂ-monicCoefficients : ∀ {n} (p : MonicPolynomial n) z →
    evaluatePolynomialℂ (monicCoefficients p) z ≡ evaluateMonic p z
  evaluatePolynomialℂ-monicCoefficients = D.evaluate-monicCoefficients

  polynomialDerivativeℂ-monicCoefficients : ∀ {n} (p : MonicPolynomial n) z →
    polynomialDerivativeℂ (monicCoefficients p) z ≡ derivativeMonic p z
  polynomialDerivativeℂ-monicCoefficients = D.derivative-monicCoefficients
