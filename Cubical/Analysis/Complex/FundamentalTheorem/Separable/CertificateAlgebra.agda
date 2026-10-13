module Cubical.Analysis.Complex.FundamentalTheorem.Separable.CertificateAlgebra where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (zero; suc)
open import Cubical.Data.List using ([]; _∷_)
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver
import Cubical.Analysis.Complex.Polynomial.Algebra as PolynomialDefinition
import Cubical.Analysis.Complex.Polynomial.MonicAlgebra as MonicDefinition
import Cubical.Analysis.Complex.Polynomial.Differential.Algebra as DifferentialDefinition
import Cubical.Analysis.Complex.Polynomial.Differential.MonicAlgebra as MonicDifferentialDefinition
import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.PolynomialAlgebra as CertificatesDefinition

module CertificateLaws {ℓ} (R : CommRing ℓ) where
  open CommRingStr (snd R)
  open PolynomialDefinition.Polynomials R
  open MonicDefinition.Monic R
  open DifferentialDefinition.Differential R
  open MonicDifferentialDefinition.MonicDifferential R
  open CertificatesDefinition.Certificates R

  private
    zeroHorner : ∀ z → 0r + z · 0r ≡ 0r
    zeroHorner z = solve! R

  -- Zero-extended coefficient equality respects Horner evaluation, including
  -- different list lengths. There is no coefficient zero test.
  evaluate-identity : ∀ p q → PolynomialIdentity p q → ∀ z → evaluate p z ≡ evaluate q z
  evaluate-identity [] [] equal z = refl
  evaluate-identity [] (b ∷ q) equal z = sym (zeroHorner z)
    ∙ cong₂ (λ a v → a + z · v) (equal zero)
      (evaluate-identity [] q (λ k → equal (suc k)) z)
  evaluate-identity (a ∷ p) [] equal z =
    cong₂ (λ a v → a + z · v) (equal zero)
      (evaluate-identity p [] (λ k → equal (suc k)) z)
    ∙ zeroHorner z
  evaluate-identity (a ∷ p) (b ∷ q) equal z =
    cong₂ (λ a v → a + z · v) (equal zero)
      (evaluate-identity p q (λ k → equal (suc k)) z)

  private
    evaluateBezoutExpression : ∀ {n} (p : MonicPolynomial n) s t z →
      evaluate (addCoefficients (multiplyCoefficients s (monicCoefficients p))
        (multiplyCoefficients t (differentiate (monicCoefficients p)))) z ≡
      evaluate s z · evaluateMonic p z + evaluate t z · derivativeMonic p z
    evaluateBezoutExpression p s t z =
      evaluate-add (multiplyCoefficients s (monicCoefficients p))
        (multiplyCoefficients t (differentiate (monicCoefficients p))) z
      ∙ cong₂ _+_
        (evaluate-multiply s (monicCoefficients p) z
          ∙ cong (evaluate s z ·_) (evaluate-monicCoefficients p z))
        (evaluate-multiply t (differentiate (monicCoefficients p)) z
          ∙ cong (evaluate t z ·_)
            (evaluate-differentiate (monicCoefficients p) z ∙ derivative-monicCoefficients p z))

    unitPolynomial : ∀ z → evaluate (1r ∷ []) z ≡ 1r
    unitPolynomial z = solve! R

  bezout-evaluate : ∀ {n} (p : MonicPolynomial n) (certificate : BezoutSeparability p) z →
    evaluate (BezoutSeparability.bezoutS certificate) z · evaluateMonic p z +
    evaluate (BezoutSeparability.bezoutT certificate) z · derivativeMonic p z ≡ 1r
  bezout-evaluate p certificate z = sym (evaluateBezoutExpression p s t z)
    ∙ evaluate-identity
      (addCoefficients (multiplyCoefficients s (monicCoefficients p))
        (multiplyCoefficients t (differentiate (monicCoefficients p))))
      (1r ∷ []) (BezoutSeparability.bezoutIdentity certificate) z
    ∙ unitPolynomial z
    where
    s = BezoutSeparability.bezoutS certificate
    t = BezoutSeparability.bezoutT certificate

  private
    removeRootTerm : ∀ a b d → a · 0r + b · d ≡ b · d
    removeRootTerm a b d = solve! R

  -- At an actual root the certificate supplies the derivative's inverse
  -- directly. No reciprocal construction or negative nonzeroness is used.
  bezout-inverseAtRoot : ∀ {n} (p : MonicPolynomial n) (certificate : BezoutSeparability p) r →
    evaluateMonic p r ≡ 0r →
    evaluate (BezoutSeparability.bezoutT certificate) r · derivativeMonic p r ≡ 1r
  bezout-inverseAtRoot p certificate r root =
    sym (removeRootTerm (evaluate s r) (evaluate t r) (derivativeMonic p r))
    ∙ cong (λ value → evaluate s r · value + evaluate t r · derivativeMonic p r) (sym root)
    ∙ bezout-evaluate p certificate r
    where
    s = BezoutSeparability.bezoutS certificate
    t = BezoutSeparability.bezoutT certificate
