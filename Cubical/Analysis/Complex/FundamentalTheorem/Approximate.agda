module Cubical.Analysis.Complex.FundamentalTheorem.Approximate where

open import Cubical.Foundations.Prelude
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Complex.FundamentalTheorem.Statement
open import Cubical.Analysis.Complex.FundamentalTheorem.Reduction
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.Approximate
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.Factor
open import Cubical.Analysis.Complex.FundamentalTheorem.Descent.Uniform

-- Each tolerance receives a truncated finite witness. No compatible
-- root sequence or choice principle is needed.
approximatePolynomialRoots : ApproximateRootExistence
approximatePolynomialRoots = uniformDescent→approximateRoots
  (λ n → descentContraction n ,
    <ℝ-weaken 0ℝ (descentContraction n) (descentContraction-positive n) ,
    descentContraction<one n , uniformPolynomialDescent n)

approximateFundamentalTheorem : ApproximateFundamentalTheorem
approximateFundamentalTheorem = approximateRoots→factorization approximatePolynomialRoots
