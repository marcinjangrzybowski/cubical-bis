module Cubical.Analysis.Complex.FundamentalTheorem.Reduction where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Vec using (Vec; []; _∷_)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open PositiveRationals.PositiveHalvesℚ using (_/2₊)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.Polynomial.Monic.Metric
open import Cubical.Analysis.Complex.Polynomial.Monic.Continuity
open import Cubical.Analysis.Complex.FundamentalTheorem.Statement

-- The induction uses only finitely many truncated witnesses for each
-- polynomial/tolerance. The Approximate module supplies the approximate-root
-- premise using finite uniform descent; no convergence witness is selected.
approximateRoots→factorization : ApproximateRootExistence → ApproximateFundamentalTheorem
approximateRoots→factorization roots zero [] ε = ∣ [] , (λ ()) ∣₁
approximateRoots→factorization roots (suc n) p ε = PT.rec squash₁ atRoot (roots n p (ε /2₊))
  where
  atRoot : (Σ[ r ∈ ℂ ] (evaluateMonic p r ∼ℂ[ ε /2₊ ] 0ℂ)) → ApproximateFactorization p ε
  atRoot (r , small) = PT.rec squash₁ atRadius
    (multiplyLinear-coefficientContinuous r quotient (ε /2₊))
    where
    quotient : MonicPolynomial n
    quotient = quotientMonic p r

    remainder-close : CoefficientCloseness p (ε /2₊) (multiplyLinear r quotient)
    remainder-close = subst (λ q → CoefficientCloseness q (ε /2₊) (multiplyLinear r quotient))
      (sym (reconstructMonic p r))
      (addConstant-small (evaluateMonic p r) (multiplyLinear r quotient) (ε /2₊) small)

    atRadius : (Σ[ δ ∈ ℚ₊ ] ((q : MonicPolynomial n) →
      CoefficientCloseness quotient δ q →
      CoefficientCloseness (multiplyLinear r quotient) (ε /2₊) (multiplyLinear r q))) →
      ApproximateFactorization p ε
    atRadius (δ , continuous) = PT.map
      (λ (rs , close) → (r ∷ rs) ,
        coefficientCloseness-halfTriangle p (multiplyLinear r quotient)
          (multiplyLinear r (linearFactors rs)) ε remainder-close (continuous (linearFactors rs) close))
      (approximateRoots→factorization roots n quotient δ)
