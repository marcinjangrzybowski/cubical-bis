module Cubical.Analysis.Complex.Polynomial.RootCertificate where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List using (List)
open import Cubical.Data.Sigma
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Contraction
open import Cubical.Analysis.Complex.Polynomial.Base
open import Cubical.Analysis.Complex.Polynomial.Bounds

private
  subtractZero : ∀ z → z -ℂ 0ℂ ≡ z
  subtractZero z = cong (z +ℂ_) ℂRing.0Selfinverse ∙ +ℂIdR z

-- These are finite coefficient inequalities. No convergence or existence
-- witness is required from the caller: Iteration constructs the witness.
module PolynomialFixedPoint (coefficients : List ℂ) (radius q : ℝ)
  (radius-nonnegative : 0ℝ ≤ℝ radius)
  (q-nonnegative : 0ℝ ≤ℝ q) (q<one : q <ℝ 1ℝ)
  (bounded : polynomialBoundℂ coefficients radius ≤ℝ radius)
  (lipschitz : polynomialLipschitzBoundℂ coefficients radius ≤ℝ q) where

  private
    f : ℂ → ℂ
    f = evaluatePolynomialℂ coefficients

    ball→norm : ∀ z → ComplexBall 0ℂ radius z → normℂ z ≤ℝ radius
    ball→norm z = subst (_≤ℝ radius) (cong normℂ (subtractZero z))

    preserves : ∀ z → ComplexBall 0ℂ radius z → ComplexBall 0ℂ radius (f z)
    preserves z zb = subst (_≤ℝ radius) (sym (cong normℂ (subtractZero (f z))))
      (≤ℝ-trans (normℂ (f z)) (polynomialBoundℂ coefficients radius) radius
        (evaluatePolynomialℂ-bound coefficients radius z (ball→norm z zb)) bounded)

    contracts : ∀ z w → ComplexBall 0ℂ radius z → ComplexBall 0ℂ radius w →
      normℂ (f z -ℂ f w) ≤ℝ q · normℂ (z -ℂ w)
    contracts z w zb wb = ≤ℝ-trans (normℂ (f z -ℂ f w))
      (polynomialLipschitzBoundℂ coefficients radius · normℂ (z -ℂ w))
      (q · normℂ (z -ℂ w))
      (evaluatePolynomialℂ-lipschitz coefficients radius z w (ball→norm z zb) (ball→norm w wb))
      (mulPres≤R-0≤ (polynomialLipschitzBoundℂ coefficients radius) q (normℂ (z -ℂ w))
        (normℂ-nonnegative (z -ℂ w)) lipschitz)

    module I = Iteration f 0ℂ radius q radius-nonnegative q-nonnegative q<one preserves contracts

  opaque
    polynomialFixedPoint : Σ[ z ∈ ℂ ] ((normℂ z ≤ℝ radius) × (f z ≡ z))
    polynomialFixedPoint = I.value , ball→norm I.value I.value-inBall , I.value-fixed

    polynomialFixedPoint-unique : ∀ z → normℂ z ≤ℝ radius → f z ≡ z →
      z ≡ fst polynomialFixedPoint
    polynomialFixedPoint-unique z zb fixed = I.value-unique z
      (subst (_≤ℝ radius) (sym (cong normℂ (subtractZero z))) zb) fixed

    certifiedPolynomialRoot : Σ[ z ∈ ℂ ] ((normℂ z ≤ℝ radius) ×
      (evaluatePolynomialℂ (subtractVariablePolynomialℂ coefficients) z ≡ 0ℂ))
    certifiedPolynomialRoot = fst polynomialFixedPoint , fst (snd polynomialFixedPoint) ,
      (evaluatePolynomialℂ-subtractVariable coefficients (fst polynomialFixedPoint)
      ∙ cong (_-ℂ fst polynomialFixedPoint) (snd (snd polynomialFixedPoint))
      ∙ +ℂInvR (fst polynomialFixedPoint))
