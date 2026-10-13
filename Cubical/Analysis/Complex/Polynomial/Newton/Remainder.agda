module Cubical.Analysis.Complex.Polynomial.Newton.Remainder where

open import Cubical.Foundations.Prelude
open import Cubical.Analysis.Real.Base using (ℝ)
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Norm.Bounds
open import Cubical.Analysis.Complex.Contraction using (ComplexBall)
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.Polynomial.Base
open import Cubical.Analysis.Complex.Polynomial.Differential
open import Cubical.Analysis.Complex.Polynomial.Differential.Monic
open import Cubical.Analysis.Complex.Polynomial.Differential.Estimates
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.LocalRoots using (NewtonErrorBound)
import Cubical.Analysis.Complex.Polynomial.Differential.DividedDifferenceAlgebra as Identities

private module C = Identities.DividedDifferenceIdentities ℂCommRing

opaque
  -- A center bound expands by the radius to cover the entire closed ball.
  normℂ-ballBound : ∀ center bound radius z → normℂ center ≤ℝ bound →
    ComplexBall center radius z → normℂ z ≤ℝ bound + radius
  normℂ-ballBound center bound radius z cb zb =
    subst2 _≤ℝ_ (sym (cong normℂ (C.recover z center))) (addComm radius bound)
      (normℂ-addBound (z -ℂ center) center radius bound zb cb)

  monicNewtonRemainder-bound : ∀ {n} (p : MonicPolynomial n) center bound radius z w →
    normℂ center ≤ℝ bound → normℂ z ≤ℝ bound → normℂ w ≤ℝ bound →
    ComplexBall center radius z → ComplexBall center radius w →
    normℂ ((evaluateMonic p z -ℂ evaluateMonic p w) -ℂ
      derivativeMonic p center ·ℂ (z -ℂ w)) ≤ℝ
      (polynomialDerivativeVariationℂ (monicCoefficients p) bound · radius) · normℂ (z -ℂ w)
  monicNewtonRemainder-bound p center bound radius z w cb zb wb zr wr =
    subst (_≤ℝ (polynomialDerivativeVariationℂ (monicCoefficients p) bound · radius) · normℂ (z -ℂ w))
      (cong normℂ (cong₂ _-ℂ_
        (cong₂ _-ℂ_ (evaluatePolynomialℂ-monicCoefficients p z) (evaluatePolynomialℂ-monicCoefficients p w))
        (cong (_·ℂ (z -ℂ w)) (polynomialDerivativeℂ-monicCoefficients p center))))
      (polynomialNewtonRemainder-boundℂ (monicCoefficients p) bound radius center z w cb zb wb zr wr)

  -- An inhabitant of the exact remainder hypothesis of localNewtonRoot.
  -- This leaves only scalar smallness and inverse estimates to its caller.
  polynomialNewtonErrorBound : ∀ {n} (p : MonicPolynomial n) center bound radius →
    normℂ center ≤ℝ bound → 0ℝ ≤ℝ radius →
    NewtonErrorBound p center radius
      (polynomialDerivativeVariationℂ (monicCoefficients p) (bound + radius) · radius)
  polynomialNewtonErrorBound p center bound radius cb rn z w zb wb =
    monicNewtonRemainder-bound p center (bound + radius) radius z w
      center-bound (normℂ-ballBound center bound radius z cb zb)
      (normℂ-ballBound center bound radius w cb wb) zb wb
    where
    center-bound : normℂ center ≤ℝ bound + radius
    center-bound = ≤ℝ-trans (normℂ center) bound (bound + radius) cb
      (subst (_≤ℝ bound + radius) (addIdR bound) (addPres≤L 0ℝ radius bound rn))
