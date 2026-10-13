module Cubical.Analysis.Complex.Polynomial.Expansion.Bounds where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData as Fin using (Fin; zero; suc)
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Addition
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Modulus.Base
open import Cubical.Analysis.Complex.Modulus.Bounds
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.Polynomial.FiniteSumAlgebra
open import Cubical.Analysis.Complex.Polynomial.Expansion
open import Cubical.Analysis.Complex.Polynomial.Expansion.Modulus public

private
  module ComplexSum = FiniteSums ℂCommRing
  module RealSum = FiniteSums ℝCommRing

nonconstantWeight : ∀ {n} → MonicPolynomial (suc n) → ℝ → Fin (suc n) → ℝ
nonconstantWeight p radius i = modulusℂ (monicCoefficient p (suc i)) · powℝ radius (suc (Fin.toℕ i))

private
  opaque
    coefficientPowerModulus : ∀ a z n →
      modulusℂ (a ·ℂ (z ^ℂ n)) ≡ modulusℂ a · powℝ (modulusℂ z) n
    coefficientPowerModulus a z n = modulusℂ-mul a (z ^ℂ n)
      ∙ cong (modulusℂ a ·_) (modulusℂ-power z n)

opaque
  modulusℂ-nonconstantTerm : ∀ {n} (p : MonicPolynomial (suc n)) z i →
    modulusℂ (nonconstantTerm p z i) ≡ nonconstantWeight p (modulusℂ z) i
  modulusℂ-nonconstantTerm p z i = cong modulusℂ (nonconstantTerm-formula p z i)
    ∙ coefficientPowerModulus (monicCoefficient p (suc i)) z (suc (Fin.toℕ i))

private
  opaque
    selectedTriangle : ∀ value pair rest bound → value ≡ pair +ℂ rest → modulusℂ rest ≤ℝ bound →
      modulusℂ value ≤ℝ modulusℂ pair + bound
    selectedTriangle value pair rest bound equation bounded =
      subst (λ x → modulusℂ x ≤ℝ modulusℂ pair + bound) (sym equation)
        (≤ℝ-trans (modulusℂ (pair +ℂ rest)) (modulusℂ pair + modulusℂ rest) (modulusℂ pair + bound)
          (modulusℂ-triangle pair rest) (addPres≤L (modulusℂ rest) bound (modulusℂ pair) bounded))

    sumExceptBound : ∀ {n} (values : Fin n → ℂ) (bounds : Fin n → ℝ) k →
      (∀ i → modulusℂ (values i) ≡ bounds i) →
      modulusℂ (ComplexSum.sumExcept values k) ≤ℝ RealSum.sumExcept bounds k
    sumExceptBound values bounds k equation =
      subst (modulusℂ (ComplexSum.sumExcept values k) ≤ℝ_)
        (cong (λ f → RealSum.sumExcept f k) (funExt equation)) (modulusℂ-sumExcept values k)

evaluateMonic-selectedBound : ∀ {n} (p : MonicPolynomial (suc n)) z k →
  modulusℂ (evaluateMonic p z) ≤ℝ modulusℂ (monicCoefficient p zero +ℂ nonconstantTerm p z k) +
    RealSum.sumExcept (nonconstantWeight p (modulusℂ z)) k
evaluateMonic-selectedBound p z k =
  selectedTriangle (evaluateMonic p z) pair rest bound (evaluateMonic-selectTerm p z k)
    (sumExceptBound (nonconstantTerm p z) (nonconstantWeight p (modulusℂ z)) k
      (modulusℂ-nonconstantTerm p z))
  where
  pair = monicCoefficient p zero +ℂ nonconstantTerm p z k
  rest = ComplexSum.sumExcept (nonconstantTerm p z) k
  bound = RealSum.sumExcept (nonconstantWeight p (modulusℂ z)) k
