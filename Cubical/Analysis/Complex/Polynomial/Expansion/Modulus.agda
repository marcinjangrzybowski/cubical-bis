module Cubical.Analysis.Complex.Polynomial.Expansion.Modulus where

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

private
  module ComplexSum = FiniteSums ℂCommRing
  module RealSum = FiniteSums ℝCommRing
opaque

  modulusℂ-power : ∀ z n → modulusℂ (z ^ℂ n) ≡ powℝ (modulusℂ z) n
  modulusℂ-power z zero = modulusℂ-one
  modulusℂ-power z (suc n) = modulusℂ-mul z (z ^ℂ n) ∙ cong (modulusℂ z ·_) (modulusℂ-power z n)

  modulusℂ-sumTerms : ∀ {n} (values : Fin n → ℂ) →
    modulusℂ (ComplexSum.sumTerms values) ≤ℝ RealSum.sumTerms (λ i → modulusℂ (values i))
  modulusℂ-sumTerms {zero} values = subst (_≤ℝ 0ℝ) (sym modulusℂ-zero) (≤ℝ-refl 0ℝ)
  modulusℂ-sumTerms {suc n} values =
    ≤ℝ-trans (modulusℂ (ComplexSum.sumTerms values))
      (modulusℂ (values zero) + modulusℂ (ComplexSum.sumTerms (λ i → values (suc i))))
      (RealSum.sumTerms (λ i → modulusℂ (values i)))
      (modulusℂ-triangle (values zero) (ComplexSum.sumTerms (λ i → values (suc i))))
      (addPres≤L (modulusℂ (ComplexSum.sumTerms (λ i → values (suc i))))
        (RealSum.sumTerms (λ i → modulusℂ (values (suc i)))) (modulusℂ (values zero))
        (modulusℂ-sumTerms (λ i → values (suc i))))

  modulusℂ-sumExcept : ∀ {n} (values : Fin n → ℂ) k →
    modulusℂ (ComplexSum.sumExcept values k) ≤ℝ RealSum.sumExcept (λ i → modulusℂ (values i)) k
  modulusℂ-sumExcept {suc n} values zero = modulusℂ-sumTerms (λ i → values (suc i))
  modulusℂ-sumExcept {suc n} values (suc k) =
    ≤ℝ-trans (modulusℂ (ComplexSum.sumExcept values (suc k)))
      (modulusℂ (values zero) + modulusℂ (ComplexSum.sumExcept (λ i → values (suc i)) k))
      (RealSum.sumExcept (λ i → modulusℂ (values i)) (suc k))
      (modulusℂ-triangle (values zero) (ComplexSum.sumExcept (λ i → values (suc i)) k))
      (addPres≤L (modulusℂ (ComplexSum.sumExcept (λ i → values (suc i)) k))
        (RealSum.sumExcept (λ i → modulusℂ (values (suc i))) k) (modulusℂ (values zero))
        (modulusℂ-sumExcept (λ i → values (suc i)) k))

