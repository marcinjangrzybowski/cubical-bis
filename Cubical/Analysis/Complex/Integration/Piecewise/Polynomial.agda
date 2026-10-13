module Cubical.Analysis.Complex.Integration.Piecewise.Polynomial where

open import Cubical.Foundations.Prelude
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Polynomial.Base
open import Cubical.Analysis.Complex.Polynomial.Differential
open import Cubical.Analysis.Complex.Integration.Path
open import Cubical.Analysis.Complex.Integration.LineIntegral.Base
open import Cubical.Analysis.Complex.Integration.LineIntegral.Polynomial
open import Cubical.Analysis.Complex.Integration.Piecewise.Base
open import Cubical.Analysis.Complex.Integration.Piecewise.FundamentalTheorem

polynomialDerivativeHasPiecewiseComplexLineIntegral : ∀ {z w} (chain : PiecewiseComplexPath z w) p →
  HasPiecewiseComplexLineIntegral (polynomialDerivativeℂ p) chain (evaluatePolynomialℂ p w -ℂ evaluatePolynomialℂ p z)
polynomialDerivativeHasPiecewiseComplexLineIntegral chain p =
  piecewisePrimitiveFromPieceIntegrals (evaluatePolynomialℂ p) (polynomialDerivativeℂ p) chain
    (allComplexPieces (λ path → HasComplexLineIntegral (polynomialDerivativeℂ p) path
      (evaluatePolynomialℂ p (pathFinish path) -ℂ evaluatePolynomialℂ p (pathStart path)))
      (λ path → polynomialDerivativeHasComplexLineIntegral path p) chain)

closedPolynomialDerivativeHasZeroPiecewiseIntegral : ∀ {z} (chain : PiecewiseComplexPath z z) p →
  HasPiecewiseComplexLineIntegral (polynomialDerivativeℂ p) chain 0ℂ
closedPolynomialDerivativeHasZeroPiecewiseIntegral {z} chain p =
  subst (HasPiecewiseComplexLineIntegral (polynomialDerivativeℂ p) chain) (+ℂInvR (evaluatePolynomialℂ p z))
    (polynomialDerivativeHasPiecewiseComplexLineIntegral chain p)
