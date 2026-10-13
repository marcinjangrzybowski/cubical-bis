module Cubical.Analysis.Complex.Calculus.Derivative.Polynomial where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Continuity
open import Cubical.Analysis.Complex.Polynomial.Base
open import Cubical.Analysis.Complex.Polynomial.Differential
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.Polynomial.Differential.Monic
open import Cubical.Analysis.Complex.Calculus.Derivative.Base
open import Cubical.Analysis.Complex.Calculus.Derivative.Factor

polynomialℂ-isContinuous : ∀ p →
  isContinuous (ℂPremetricSpace .snd) (evaluatePolynomialℂ p) (ℂPremetricSpace .snd)
polynomialℂ-isContinuous [] = subst
  (λ f → isContinuous (ℂPremetricSpace .snd) f (ℂPremetricSpace .snd))
  (sym (funExt evaluatePolynomialℂ-empty)) (constantℂ-isContinuous (ℂPremetricSpace .snd) 0ℂ)
polynomialℂ-isContinuous (a ∷ p) = subst
  (λ f → isContinuous (ℂPremetricSpace .snd) f (ℂPremetricSpace .snd))
  (sym (funExt (evaluatePolynomialℂ-cons a p)))
  (addOfComplexContinuous (ℂPremetricSpace .snd) (λ _ → a) (λ z → z ·ℂ evaluatePolynomialℂ p z)
    (constantℂ-isContinuous (ℂPremetricSpace .snd) a)
    (mulOfComplexContinuous (ℂPremetricSpace .snd) (idfun ℂ) (evaluatePolynomialℂ p)
      (snd (CategoryStructures.idᶜ {M = ℂPremetricSpace})) (polynomialℂ-isContinuous p)))

opaque
  -- This is the already existing formal derivative, now certified for the
  -- general analytic predicate by its continuous divided difference.
  polynomialHasComplexDerivative : ∀ p → IsComplexDerivative (evaluatePolynomialℂ p) (polynomialDerivativeℂ p)
  polynomialHasComplexDerivative p z = continuousComplexDifferenceFactorGivesDerivativeAt
    (ℂPremetricSpace .snd) (idfun ℂ) (evaluatePolynomialℂ p) (polynomialDerivativeℂ p z) z
    (evaluatePolynomialℂ (quotientPolynomialℂ p z))
    (λ w → cong (_-ℂ evaluatePolynomialℂ p z) (polynomialDivisionIdentityℂ p z w)
      ∙ cong (_-ℂ evaluatePolynomialℂ p z)
        (+ℂComm (evaluatePolynomialℂ p z) ((w -ℂ z) ·ℂ evaluatePolynomialℂ (quotientPolynomialℂ p z) w))
      ∙ ℂRing.plusMinus ((w -ℂ z) ·ℂ evaluatePolynomialℂ (quotientPolynomialℂ p z) w) (evaluatePolynomialℂ p z))
    (polynomialDividedDifference-diagonalℂ p z)
    (polynomialℂ-isContinuous (quotientPolynomialℂ p z) z)

  differentiatedPolynomialHasComplexDerivative : ∀ p →
    IsComplexDerivative (evaluatePolynomialℂ p) (evaluatePolynomialℂ (differentiatePolynomialℂ p))
  differentiatedPolynomialHasComplexDerivative p = subst (IsComplexDerivative (evaluatePolynomialℂ p))
    (sym (funExt (evaluatePolynomialℂ-differentiate p))) (polynomialHasComplexDerivative p)

  monicHasComplexDerivative : ∀ {n} (p : MonicPolynomial n) →
    IsComplexDerivative (evaluateMonic p) (derivativeMonic p)
  monicHasComplexDerivative p = subst2 IsComplexDerivative
    (funExt (evaluatePolynomialℂ-monicCoefficients p)) (funExt (polynomialDerivativeℂ-monicCoefficients p))
    (polynomialHasComplexDerivative (monicCoefficients p))

  polynomialDerivativeℂ-isContinuous : ∀ p →
    isContinuous (ℂPremetricSpace .snd) (polynomialDerivativeℂ p) (ℂPremetricSpace .snd)
  polynomialDerivativeℂ-isContinuous p = subst
    (λ f → isContinuous (ℂPremetricSpace .snd) f (ℂPremetricSpace .snd))
    (funExt (evaluatePolynomialℂ-differentiate p)) (polynomialℂ-isContinuous (differentiatePolynomialℂ p))
