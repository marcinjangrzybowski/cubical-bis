module Cubical.Analysis.Complex.FundamentalTheorem.Approximate.Norm where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Sigma
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open PositiveRationals.PositiveHalvesℚ using (_/2₊)
open import Cubical.Analysis.Real.Base using (rat)
open import Cubical.Analysis.Real.Algebra.Addition using (rat+rat)
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Norm.Metric
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.FundamentalTheorem.Approximate

approximatePolynomialRoots-norm : (n : ℕ) (p : MonicPolynomial (suc n)) (ε : ℚ₊) →
  PT.∥ Σ[ z ∈ ℂ ] normℂ (evaluateMonic p z) <ℝ rat (fst ε) ∥₁
approximatePolynomialRoots-norm n p ε = PT.map
  (λ (z , close) → z , subst (normℂ (evaluateMonic p z) <ℝ_)
    (rat+rat (fst (ε /2₊)) (fst (ε /2₊)) ∙ cong rat (1/2∈ℚ./2+/2≡id (fst ε)))
    (closeZero→normℂ-bound (evaluateMonic p z) (ε /2₊) close))
  (approximatePolynomialRoots n p (ε /2₊))
