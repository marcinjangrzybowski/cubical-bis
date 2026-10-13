module Cubical.Analysis.Complex.FundamentalTheorem.Separable.Certificate where

-- Proofs using the positive certificate specified in Formulations.Basic.
-- This bridge proves no new root-existence assertion.

open import Cubical.Foundations.Prelude
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Polynomial.Base
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.Polynomial.Differential.Monic
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Basic
  using (PolynomialIdentityℂ; BezoutSeparability)
import Cubical.Analysis.Complex.FundamentalTheorem.Separable.CertificateAlgebra as CertificateDefinition

private module C = CertificateDefinition.CertificateLaws ℂCommRing

opaque
  unfolding evaluatePolynomialℂ

  polynomialIdentity-evaluationℂ : ∀ p q → PolynomialIdentityℂ p q → ∀ z →
    evaluatePolynomialℂ p z ≡ evaluatePolynomialℂ q z
  polynomialIdentity-evaluationℂ = C.evaluate-identity

  bezoutSeparability-evaluation : ∀ {n} (p : MonicPolynomial n) (certificate : BezoutSeparability p) z →
    evaluatePolynomialℂ (BezoutSeparability.bezoutS certificate) z ·ℂ evaluateMonic p z +ℂ
    evaluatePolynomialℂ (BezoutSeparability.bezoutT certificate) z ·ℂ derivativeMonic p z ≡ 1ℂ
  bezoutSeparability-evaluation = C.bezout-evaluate

  bezoutSeparability-inverseAtRoot : ∀ {n} (p : MonicPolynomial n) (certificate : BezoutSeparability p) r →
    evaluateMonic p r ≡ 0ℂ →
    evaluatePolynomialℂ (BezoutSeparability.bezoutT certificate) r ·ℂ derivativeMonic p r ≡ 1ℂ
  bezoutSeparability-inverseAtRoot = C.bezout-inverseAtRoot
