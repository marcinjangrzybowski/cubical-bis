module Cubical.Analysis.Complex.Polynomial.Differential.MonicAlgebra where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (suc)
open import Cubical.Data.Vec using ([]; _∷_)
import Cubical.Data.List as List
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver
import Cubical.Analysis.Complex.Polynomial.Algebra as PolynomialDefinition
import Cubical.Analysis.Complex.Polynomial.MonicAlgebra as MonicDefinition
import Cubical.Analysis.Complex.Polynomial.Differential.Algebra as DifferentialDefinition

module MonicDifferential {ℓ} (R : CommRing ℓ) where
  open CommRingStr (snd R)
  open MonicDefinition.Monic R
  private
    A = fst R
    module P = PolynomialDefinition.Polynomials R
    module D = DifferentialDefinition.Differential R

  monicCoefficients : ∀ {n} → MonicPolynomial n → List.List A
  monicCoefficients [] = 1r List.∷ List.[]
  monicCoefficients (a ∷ p) = a List.∷ monicCoefficients p

  evaluate-monicCoefficients : ∀ {n} (p : MonicPolynomial n) z →
    P.evaluate (monicCoefficients p) z ≡ evaluateMonic p z
  evaluate-monicCoefficients [] z = solve! R
  evaluate-monicCoefficients (a ∷ p) z =
    cong (λ v → a + z · v) (evaluate-monicCoefficients p z)

  derivativeMonic : ∀ {n} → MonicPolynomial n → A → A
  derivativeMonic [] z = 0r
  derivativeMonic (a ∷ p) z = evaluateMonic p z + z · derivativeMonic p z

  derivative-monicCoefficients : ∀ {n} (p : MonicPolynomial n) z →
    D.derivativeValue (monicCoefficients p) z ≡ derivativeMonic p z
  derivative-monicCoefficients [] z = solve! R
  derivative-monicCoefficients (a ∷ p) z =
    cong₂ (λ v d → v + z · d)
      (evaluate-monicCoefficients p z) (derivative-monicCoefficients p z)

  derivative-addConstant : ∀ {n} a (p : MonicPolynomial (suc n)) z →
    derivativeMonic (addConstant a p) z ≡ derivativeMonic p z
  derivative-addConstant a (b ∷ p) z = refl

  private
    linearDerivativeStep : ∀ a r z v d →
      (a + (z - r) · v) + z · (v + (z - r) · d) ≡
      (a + z · v) + (z - r) · (v + z · d)
    linearDerivativeStep a r z v d = solve! R

  derivative-multiplyLinear : ∀ {n} r (p : MonicPolynomial n) z →
    derivativeMonic (multiplyLinear r p) z ≡
      evaluateMonic p z + (z - r) · derivativeMonic p z
  derivative-multiplyLinear r [] z = solve! R
  derivative-multiplyLinear r (a ∷ p) z =
    cong₂ (λ v d → v + z · d)
      (evaluate-addConstant a (multiplyLinear r p) z
        ∙ cong (a +_) (evaluate-multiplyLinear r p z))
      (derivative-addConstant a (multiplyLinear r p) z
        ∙ derivative-multiplyLinear r p z)
    ∙ linearDerivativeStep a r z (evaluateMonic p z) (derivativeMonic p z)

  derivative-atRoot : ∀ {n} (p : MonicPolynomial (suc n)) r →
    evaluateMonic p r ≡ 0r →
    derivativeMonic p r ≡ evaluateMonic (quotientMonic p r) r
  derivative-atRoot p r root =
    cong (λ q → derivativeMonic q r) (factorMonicAtRoot p r root)
    ∙ derivative-multiplyLinear r (quotientMonic p r) r
    ∙ finish (evaluateMonic (quotientMonic p r) r) (derivativeMonic (quotientMonic p r) r)
    where
    finish : ∀ v d → v + (r - r) · d ≡ v
    finish v d = solve! R
