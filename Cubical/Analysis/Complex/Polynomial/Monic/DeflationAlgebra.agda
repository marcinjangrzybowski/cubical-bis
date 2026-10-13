module Cubical.Analysis.Complex.Polynomial.Monic.DeflationAlgebra where

-- Synthetic division removes a supplied linear factor coefficientwise,
-- over any commutative ring. No test for roots or cancellation axiom is
-- needed; this is the algebraic step used by quantitative root matching.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (suc)
open import Cubical.Data.Vec using ([]; _∷_)
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver
import Cubical.Analysis.Complex.Polynomial.MonicAlgebra as MonicDefinition

module Deflation {ℓ} (R : CommRing ℓ) where
  open CommRingStr (snd R)
  open MonicDefinition.Monic R

  evaluate-cons : ∀ {n} a (p : MonicPolynomial n) z →
    evaluateMonic (a ∷ p) z ≡ a + z · evaluateMonic p z
  evaluate-cons a p z = refl

  product-cons : ∀ {n} r (roots : MonicPolynomial n) z →
    productOfLinearFactors (r ∷ roots) z ≡ (z - r) · productOfLinearFactors roots z
  product-cons r roots z = refl

  quotient-cons : ∀ {n} a (p : MonicPolynomial (suc n)) r →
    quotientMonic (a ∷ p) r ≡ evaluateMonic p r ∷ quotientMonic p r
  quotient-cons a (b ∷ p) r = refl

  quotient-addConstant : ∀ {n} a (p : MonicPolynomial (suc n)) r →
    quotientMonic (addConstant a p) r ≡ quotientMonic p r
  quotient-addConstant a (b ∷ []) r = refl
  quotient-addConstant a (b ∷ c ∷ p) r = refl

  private
    vanish : ∀ r a b → a + (r - r) · b ≡ a
    vanish r a b = solve! R

  quotient-multiplyLinear : ∀ {n} r (p : MonicPolynomial n) →
    quotientMonic (multiplyLinear r p) r ≡ p
  quotient-multiplyLinear r [] = refl
  quotient-multiplyLinear r (a ∷ p) =
    quotient-cons ((- r) · a) (addConstant a (multiplyLinear r p)) r ∙ cong₂ _∷_
    (evaluate-addConstant a (multiplyLinear r p) r
      ∙ cong (a +_) (evaluate-multiplyLinear r p r)
      ∙ vanish r a (evaluateMonic p r))
    (quotient-addConstant a (multiplyLinear r p) r ∙ quotient-multiplyLinear r p)
