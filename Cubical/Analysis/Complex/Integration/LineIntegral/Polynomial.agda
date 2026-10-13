module Cubical.Analysis.Complex.Integration.LineIntegral.Polynomial where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Archimedean
open import Cubical.Analysis.Real.Order.Strict.Properties using (<ℝ-weaken)
open import Cubical.Analysis.Real.Domain.Interval
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Polynomial.Base
open import Cubical.Analysis.Complex.Polynomial.Bounds
open import Cubical.Analysis.Complex.Polynomial.Differential
open import Cubical.Analysis.Complex.Polynomial.Differential.Estimates
open import Cubical.Analysis.Complex.Calculus.Derivative.Uniform.Polynomial
open import Cubical.Analysis.Complex.Integration.Path
open import Cubical.Analysis.Complex.Integration.Path.Continuity
open import Cubical.Analysis.Complex.Integration.Path.Bounds
open import Cubical.Analysis.Complex.Integration.LineIntegral.Base
open import Cubical.Analysis.Complex.Integration.LineIntegral.FundamentalTheorem

polynomialIsUniformPrimitiveAlongPath : ∀ {a b} (path : UniformComplexPath a b) p →
  IsUniformPrimitiveAlongPath (evaluatePolynomialℂ p) (polynomialDerivativeℂ p) path
polynomialIsUniformPrimitiveAlongPath {a} {b} path p =
  polynomialHasUniformComplexDerivativeAlong (ClosedIntervalPremetricSpace a b .snd)
    (UniformComplexPath.curve path ∘ fst) p (pathImageNormBound path)
    (λ x → pathImageIsBounded path (fst x) (fst (snd x)) (snd (snd x)))
    (pathIsRadiuswiseUniformlyContinuous path)

-- A concrete family of primitives: for every complex polynomial and every
-- certified path, integration of the existing formal derivative has the
-- expected endpoint value. Both required estimates are constructed here.
-- A single merely existing rational bound is eliminated into the integral
-- proposition, not selected as an additional global datum.
opaque
  polynomialDerivativeHasComplexLineIntegral : ∀ {a b} (path : UniformComplexPath a b) p →
    HasComplexLineIntegral (polynomialDerivativeℂ p) path
      (evaluatePolynomialℂ p (pathFinish path) -ℂ evaluatePolynomialℂ p (pathStart path))
  polynomialDerivativeHasComplexLineIntegral path p = PT.rec
    (isPropHasComplexLineIntegral (polynomialDerivativeℂ p) path
      (evaluatePolynomialℂ p (pathFinish path) -ℂ evaluatePolynomialℂ p (pathStart path)))
    (λ { (n , bounded) → fundamentalTheoremOfComplexLineIntegrals path
      (evaluatePolynomialℂ p) (polynomialDerivativeℂ p) (naturalBound n)
      (λ t lower upper → ≤ℝ-trans (normℂ (polynomialDerivativeℂ p (UniformComplexPath.curve path t)))
        (polynomialLipschitzBoundℂ p (pathImageNormBound path)) (rat (naturalRational n))
        (polynomialDerivative-boundℂ p (pathImageNormBound path) (UniformComplexPath.curve path t)
          (pathImageIsBounded path t lower upper))
        (<ℝ-weaken (polynomialLipschitzBoundℂ p (pathImageNormBound path)) (rat (naturalRational n)) bounded))
      (polynomialIsUniformPrimitiveAlongPath path p) })
    (∃naturalUpperBound (polynomialLipschitzBoundℂ p (pathImageNormBound path)))

polynomialDerivativeComplexLineIntegrable : ∀ {a b} (path : UniformComplexPath a b) p →
  IsComplexLineIntegrable (polynomialDerivativeℂ p) path
polynomialDerivativeComplexLineIntegrable path p =
  (evaluatePolynomialℂ p (pathFinish path) -ℂ evaluatePolynomialℂ p (pathStart path)) ,
  polynomialDerivativeHasComplexLineIntegral path p

closedPolynomialDerivativeHasZeroLineIntegral : ∀ {a b} (path : UniformComplexPath a b) p →
  pathFinish path ≡ pathStart path → HasComplexLineIntegral (polynomialDerivativeℂ p) path 0ℂ
closedPolynomialDerivativeHasZeroLineIntegral path p closed =
  subst (HasComplexLineIntegral (polynomialDerivativeℂ p) path)
    (cong (λ z → evaluatePolynomialℂ p z -ℂ evaluatePolynomialℂ p (pathStart path)) closed
      ∙ +ℂInvR (evaluatePolynomialℂ p (pathStart path))) (polynomialDerivativeHasComplexLineIntegral path p)
