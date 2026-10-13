module Cubical.Analysis.Complex.Polynomial.Differential where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List using (List)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Polynomial.Base
import Cubical.Analysis.Complex.Polynomial.Differential.Algebra as DifferentialDefinition

private module D = DifferentialDefinition.Differential ℂCommRing

open D public using () renaming
  (differentiate to differentiatePolynomialℂ;
   quadraticRemainder to quadraticRemainderPolynomialℂ;
   translate to translatePolynomialℂ;
   centeredRemainder to centeredRemainderPolynomialℂ)

opaque
  unfolding evaluatePolynomialℂ

  polynomialDerivativeℂ : List ℂ → ℂ → ℂ
  polynomialDerivativeℂ = D.derivativeValue

  evaluatePolynomialℂ-differentiate : ∀ p z →
    evaluatePolynomialℂ (differentiatePolynomialℂ p) z ≡ polynomialDerivativeℂ p z
  evaluatePolynomialℂ-differentiate = D.evaluate-differentiate

  polynomialDividedDifference-diagonalℂ : ∀ p r →
    evaluatePolynomialℂ (quotientPolynomialℂ p r) r ≡ polynomialDerivativeℂ p r
  polynomialDividedDifference-diagonalℂ = D.dividedDifference-diagonal

  polynomialTaylorIdentityℂ : ∀ p r z → evaluatePolynomialℂ p z ≡
    evaluatePolynomialℂ p r +ℂ (z -ℂ r) ·ℂ
      (polynomialDerivativeℂ p r +ℂ
        (z -ℂ r) ·ℂ evaluatePolynomialℂ (quadraticRemainderPolynomialℂ p r) z)
  polynomialTaylorIdentityℂ = D.taylorIdentity

  evaluatePolynomialℂ-translate : ∀ p r z →
    evaluatePolynomialℂ (translatePolynomialℂ p r) z ≡ evaluatePolynomialℂ p (r +ℂ z)
  evaluatePolynomialℂ-translate = D.evaluate-translate

  polynomialCenteredTaylorIdentityℂ : ∀ p r u → evaluatePolynomialℂ p (r +ℂ u) ≡
    evaluatePolynomialℂ p r +ℂ u ·ℂ
      (polynomialDerivativeℂ p r +ℂ
        u ·ℂ evaluatePolynomialℂ (centeredRemainderPolynomialℂ p r) u)
  polynomialCenteredTaylorIdentityℂ = D.centeredTaylorIdentity
