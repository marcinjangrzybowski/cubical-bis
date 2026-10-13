module Cubical.Analysis.Complex.Polynomial.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
import Cubical.Analysis.Complex.Polynomial.Algebra as PolynomialDefinition

private module P = PolynomialDefinition.Polynomials ℂCommRing

open P public using ()
  renaming (addCoefficients to addPolynomialsℂ;
    scaleCoefficients to scalePolynomialℂ;
    multiplyCoefficients to multiplyPolynomialsℂ;
    quotientAt to quotientPolynomialℂ; subtractVariable to subtractVariablePolynomialℂ)

-- An opaque evaluator with computation paths prevents repeated expansion
-- of completed real arithmetic in analytic estimates.
opaque
  evaluatePolynomialℂ : List ℂ → ℂ → ℂ
  evaluatePolynomialℂ = P.evaluate

  evaluatePolynomialℂ-empty : ∀ z → evaluatePolynomialℂ [] z ≡ 0ℂ
  evaluatePolynomialℂ-empty z = refl

  evaluatePolynomialℂ-cons : ∀ a p z →
    evaluatePolynomialℂ (a ∷ p) z ≡ a +ℂ z ·ℂ evaluatePolynomialℂ p z
  evaluatePolynomialℂ-cons a p z = refl

  evaluatePolynomialℂ-add : ∀ p q z →
    evaluatePolynomialℂ (addPolynomialsℂ p q) z ≡ evaluatePolynomialℂ p z +ℂ evaluatePolynomialℂ q z
  evaluatePolynomialℂ-add = P.evaluate-add

  evaluatePolynomialℂ-scale : ∀ a p z →
    evaluatePolynomialℂ (scalePolynomialℂ a p) z ≡ a ·ℂ evaluatePolynomialℂ p z
  evaluatePolynomialℂ-scale = P.evaluate-scale

  evaluatePolynomialℂ-multiply : ∀ p q z →
    evaluatePolynomialℂ (multiplyPolynomialsℂ p q) z ≡ evaluatePolynomialℂ p z ·ℂ evaluatePolynomialℂ q z
  evaluatePolynomialℂ-multiply = P.evaluate-multiply

  polynomialDivisionIdentityℂ : ∀ p r z → evaluatePolynomialℂ p z ≡
    evaluatePolynomialℂ p r +ℂ (z -ℂ r) ·ℂ evaluatePolynomialℂ (quotientPolynomialℂ p r) z
  polynomialDivisionIdentityℂ = P.divisionIdentity

  polynomialFactorAtRootℂ : ∀ p r → evaluatePolynomialℂ p r ≡ 0ℂ → ∀ z →
    evaluatePolynomialℂ p z ≡ (z -ℂ r) ·ℂ evaluatePolynomialℂ (quotientPolynomialℂ p r) z
  polynomialFactorAtRootℂ = P.factorAtRoot

  evaluatePolynomialℂ-subtractVariable : ∀ p z →
    evaluatePolynomialℂ (subtractVariablePolynomialℂ p) z ≡ evaluatePolynomialℂ p z -ℂ z
  evaluatePolynomialℂ-subtractVariable = P.evaluate-subtractVariable

  evaluatePolynomialℂ-quadratic : ∀ a b c z →
    evaluatePolynomialℂ (a ∷ b ∷ c ∷ []) z ≡ a +ℂ z ·ℂ (b +ℂ z ·ℂ c)
  evaluatePolynomialℂ-quadratic = P.evaluate-quadratic
