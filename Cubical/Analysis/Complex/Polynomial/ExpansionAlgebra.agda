module Cubical.Analysis.Complex.Polynomial.ExpansionAlgebra where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData as Fin using (Fin; zero; suc)
open import Cubical.Data.Vec using ([]; _∷_)
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.Ring.Properties
open import Cubical.Analysis.Complex.Polynomial.FiniteSumAlgebra
import Cubical.Analysis.Complex.Polynomial.MonicAlgebra as MonicDefinition

module Expansion {ℓ} (R : CommRing ℓ) where
  open CommRingStr (snd R)
  open Exponentiation R
  open MonicDefinition.Monic R
  open FiniteSums R
  private
    module Sums = Sum (CommRing→Ring R)
    module Ring = RingTheory (CommRing→Ring R)

  monicCoefficient : ∀ {n} → MonicPolynomial n → Fin (suc n) → fst R
  monicCoefficient [] zero = 1r
  monicCoefficient (a ∷ p) zero = a
  monicCoefficient (a ∷ p) (suc i) = monicCoefficient p i

  monicCoefficient-leading : ∀ {n} (p : MonicPolynomial n) → monicCoefficient p (Fin.fromℕ n) ≡ 1r
  monicCoefficient-leading [] = refl
  monicCoefficient-leading (a ∷ p) = monicCoefficient-leading p

  monicTerm : ∀ {n} → MonicPolynomial n → fst R → Fin (suc n) → fst R
  monicTerm p z i = monicCoefficient p i · z ^ Fin.toℕ i

  private
    termStep : ∀ a z n → a · (z · z ^ n) ≡ z · (a · z ^ n)
    termStep a z n = ·Assoc a z (z ^ n) ∙ cong (_· z ^ n) (·Comm a z) ∙ sym (·Assoc z a (z ^ n))

  evaluateMonic-sumTerms : ∀ {n} (p : MonicPolynomial n) z → evaluateMonic p z ≡ sumTerms (monicTerm p z)
  evaluateMonic-sumTerms [] z = sym (+IdR (1r · 1r) ∙ ·IdR 1r)
  evaluateMonic-sumTerms (a ∷ p) z = sym
    (cong₂ _+_ (·IdR a)
      (Sums.∑Ext (λ i → termStep (monicCoefficient p i) z (Fin.toℕ i))
        ∙ sym (Sums.∑Mulrdist z (monicTerm p z))
        ∙ cong (z ·_) (sym (evaluateMonic-sumTerms p z))))

  opaque
    evaluateMonic-atZero : ∀ {n} (p : MonicPolynomial (suc n)) →
      evaluateMonic p 0r ≡ monicCoefficient p zero
    evaluateMonic-atZero (a ∷ p) = cong (a +_) (Ring.0LeftAnnihilates (evaluateMonic p 0r)) ∙ +IdR a

    nonconstantTerm : ∀ {n} → MonicPolynomial (suc n) → fst R → Fin (suc n) → fst R
    nonconstantTerm p z i = monicTerm p z (suc i)

    nonconstantTerm-formula : ∀ {n} (p : MonicPolynomial (suc n)) z i →
      nonconstantTerm p z i ≡ monicCoefficient p (suc i) · z ^ suc (Fin.toℕ i)
    nonconstantTerm-formula p z i = refl

    evaluateMonic-nonconstantSum : ∀ {n} (p : MonicPolynomial (suc n)) z →
      evaluateMonic p z ≡ monicCoefficient p zero + sumTerms (nonconstantTerm p z)
    evaluateMonic-nonconstantSum p z = evaluateMonic-sumTerms p z
      ∙ cong (_+ sumTerms (nonconstantTerm p z)) (·IdR (monicCoefficient p zero))

    evaluateMonic-selectTerm : ∀ {n} (p : MonicPolynomial (suc n)) z k →
      evaluateMonic p z ≡ (monicCoefficient p zero + nonconstantTerm p z k) + sumExcept (nonconstantTerm p z) k
    evaluateMonic-selectTerm p z k = evaluateMonic-nonconstantSum p z
      ∙ cong (monicCoefficient p zero +_) (sumSplitSelected (nonconstantTerm p z) k)
      ∙ +Assoc (monicCoefficient p zero) (nonconstantTerm p z k) (sumExcept (nonconstantTerm p z) k)
