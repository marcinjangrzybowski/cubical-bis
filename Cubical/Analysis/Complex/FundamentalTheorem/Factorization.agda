module Cubical.Analysis.Complex.FundamentalTheorem.Factorization where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Vec using (Vec; []; _∷_; lookup)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open import Cubical.Analysis.Real.Base using (refl∼)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.FundamentalTheorem.Statement

linearFactorization : ∀ a → linearFactors ((-ℂ a) ∷ []) ≡ (a ∷ [])
linearFactorization a = cong (_∷ []) (ℂRing.-Idempotent a)

exactFactorization-constant : ExactFactorization []
exactFactorization-constant = ∣ [] , refl ∣₁

exactFactorization-linear : ∀ a → ExactFactorization (a ∷ [])
exactFactorization-linear a = ∣ (-ℂ a) ∷ [] , linearFactorization a ∣₁

exactFactorization-fromRoot : ∀ {n} (p : MonicPolynomial (suc n)) r →
  evaluateMonic p r ≡ 0ℂ → ExactFactorization (quotientMonic p r) → ExactFactorization p
exactFactorization-fromRoot p r root = PT.map λ (roots , factorization) →
  (r ∷ roots) , cong (multiplyLinear r) factorization ∙ sym (factorMonicAtRoot p r root)

exactFactorization-quadraticRoot : (p : MonicPolynomial 2) (r : ℂ) →
  evaluateMonic p r ≡ 0ℂ → ExactFactorization p
exactFactorization-quadraticRoot (a ∷ b ∷ []) r root =
  exactFactorization-fromRoot (a ∷ b ∷ []) r root
    (exactFactorization-linear (evaluateMonic (b ∷ []) r))

exactFactorization→approximate : ∀ {n} (p : MonicPolynomial n) →
  ExactFactorization p → ∀ ε → ApproximateFactorization p ε
exactFactorization→approximate p factorization ε = PT.map
  (λ (roots , path) → roots , λ k →
    subst (λ q → CoefficientCloseness p ε q) (sym path)
      (λ j → refl∼ (re (lookup j p)) ε , refl∼ (im (lookup j p)) ε) k)
  factorization

approximateFactorization-linear : ∀ a ε → ApproximateFactorization (a ∷ []) ε
approximateFactorization-linear a = exactFactorization→approximate (a ∷ []) (exactFactorization-linear a)
