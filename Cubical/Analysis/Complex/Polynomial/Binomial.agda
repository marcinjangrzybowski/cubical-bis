module Cubical.Analysis.Complex.Polynomial.Binomial where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (suc)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Modulus.Base
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Metric.Operations
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.Roots.Existence
open import Cubical.Analysis.Complex.Roots.Approximate
import Cubical.Analysis.Complex.Polynomial.BinomialAlgebra as BinomialDefinition

open BinomialDefinition.Binomial ℂCommRing public

binomialRoot-apart : ∀ n a → 0ℝ <ℝ modulusℂ a →
  ∥ Σ[ z ∈ ℂ ] evaluateMonic (binomial n a) z ≡ 0ℂ ∥₁
binomialRoot-apart n a positive = PT.map
  (λ (z , root) → z , evaluate-binomial n a z ∙ cong (a +ℂ_) root ∙ +ℂInvR a)
  (nonzeroComplexRoot n (-ℂ a) (subst (0ℝ <ℝ_) (sym (modulusℂ-neg a)) positive))

approximateBinomialRoot : ∀ n a (ε : ℚ₊) →
  ∥ Σ[ z ∈ ℂ ] evaluateMonic (binomial n a) z ∼ℂ[ ε ] 0ℂ ∥₁
approximateBinomialRoot n a ε = PT.map
  (λ (z , close) → z ,
    subst2 (λ x y → x ∼ℂ[ ε ] y) (sym (evaluate-binomial n a z)) (+ℂInvR a)
      (addℂ-presClosenessL a (z ^ℂ suc n) (-ℂ a) ε close))
  (approximateComplexRoot n (-ℂ a) ε)
