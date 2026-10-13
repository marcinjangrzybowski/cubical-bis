module Cubical.Analysis.Complex.FundamentalTheorem.Descent.FiniteSum where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.FinData as Fin using (Fin; zero; suc)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Algebra.Natural
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Complex.Polynomial.FiniteSumAlgebra

private
  module R = RingTheory (CommRing→Ring ℝCommRing)

open FiniteSums ℝCommRing public using ()
  renaming (sumTerms to sumRealTerms; sumExcept to sumOtherRealTerms)

private
  countScale : ∀ n x → realNatural (suc n) · x ≡ x + realNatural n · x
  countScale n x = cong (_· x) (realNatural-suc n)
    ∙ mulDistL (realNatural n) 1ℝ x ∙ cong (realNatural n · x +_) (mulIdL x)
    ∙ addComm (realNatural n · x) x

sumRealTerms-bound : ∀ {n} (values : Fin n → ℝ) B → (∀ i → values i ≤ℝ B) →
  sumRealTerms values ≤ℝ realNatural n · B
sumRealTerms-bound {zero} values B bounded = subst (0ℝ ≤ℝ_) (sym (R.0LeftAnnihilates B)) (≤ℝ-refl 0ℝ)
sumRealTerms-bound {suc n} values B bounded =
  subst (sumRealTerms values ≤ℝ_) (sym (countScale n B))
    (addPres≤ (values zero) B (sumRealTerms (λ i → values (suc i))) (realNatural n · B)
      (bounded zero) (sumRealTerms-bound (λ i → values (suc i)) B (λ i → bounded (suc i))))

sumOtherRealTerms-bound : ∀ {n} (values : Fin (suc n) → ℝ) k B →
  (∀ i → ¬ (i ≡ k) → values i ≤ℝ B) → sumOtherRealTerms values k ≤ℝ realNatural n · B
sumOtherRealTerms-bound {n} values zero B bounded =
  sumRealTerms-bound (λ i → values (suc i)) B (λ i → bounded (suc i) Fin.snotz)
sumOtherRealTerms-bound {zero} values (suc ()) B bounded
sumOtherRealTerms-bound {suc n} values (suc k) B bounded =
  subst (sumOtherRealTerms values (suc k) ≤ℝ_) (sym (countScale n B))
    (addPres≤ (values zero) B (sumOtherRealTerms (λ i → values (suc i)) k) (realNatural n · B)
      (bounded zero Fin.znots)
      (sumOtherRealTerms-bound (λ i → values (suc i)) k B
        (λ i different → bounded (suc i) (λ equal → different (Fin.injSucFin equal)))))

sumOtherRealTerms-countBound : ∀ {n} (values : Fin (suc n) → ℝ) k B → 0ℝ ≤ℝ B →
  (∀ i → ¬ (i ≡ k) → values i ≤ℝ B) → sumOtherRealTerms values k ≤ℝ realNatural (suc n) · B
sumOtherRealTerms-countBound {n} values k B nonnegative bounded =
  ≤ℝ-trans (sumOtherRealTerms values k) (realNatural n · B) (realNatural (suc n) · B)
    (sumOtherRealTerms-bound values k B bounded)
    (mulPres≤R-0≤ (realNatural n) (realNatural (suc n)) B nonnegative (realNatural-mono ℕ.≤-sucℕ))
