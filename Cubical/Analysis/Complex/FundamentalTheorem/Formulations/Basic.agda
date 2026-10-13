module Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Basic where

-- Statement catalogue, not proofs or assumed inhabitants. See
-- Complex/FTA_SURVEY_2026-10-08.md. Capitalized theorem names below denote
-- types whose inhabitants must be constructed in separate proof modules.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData using (Fin)
open import Cubical.Data.Vec using (Vec; lookup)
open import Cubical.Data.List using (List; []; _∷_)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty using (⊥)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁)
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Modulus.Base using (modulusℂ)
open import Cubical.Analysis.Complex.Polynomial.Base
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.Polynomial.Differential
open import Cubical.Analysis.Complex.Polynomial.Differential.Monic
open import Cubical.Analysis.Complex.FundamentalTheorem.Statement public
import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.PolynomialAlgebra as CertificatesDefinition

-- Ordinary coefficient lists can contain trailing zeroes. Equality of
-- polynomials therefore compares zero-extended coefficients, not lists.
open CertificatesDefinition.Certificates ℂCommRing public using () renaming
  (coefficient to polynomialCoefficientℂ; PolynomialIdentity to PolynomialIdentityℂ;
   BezoutSeparability to BezoutSeparability)

ExactRootData : ∀ {n} → MonicPolynomial n → Type₀
ExactRootData p = Σ[ z ∈ ℂ ] evaluateMonic p z ≡ 0ℂ

ExactRootExistence : Type₀
ExactRootExistence = (n : ℕ) (p : MonicPolynomial (suc n)) → ∥ ExactRootData p ∥₁

ExactFundamentalTheorem : Type₀
ExactFundamentalTheorem = (n : ℕ) (p : MonicPolynomial n) → ExactFactorization p

-- Double negation is deliberately retained. This asserts that a polynomial
-- cannot have no roots; it does not return even a truncated root witness.
WeakFundamentalTheorem : Type₀
WeakFundamentalTheorem = (n : ℕ) (p : MonicPolynomial (suc n)) →
  (∥ ExactRootData p ∥₁ → ⊥) → ⊥

-- Both finite-accuracy formulations and their direct reductions are proved;
-- see Reduction and Matching.ApproximateEquivalence for the inhabitants.
ApproximateFormulationsInterderivable : Type₀
ApproximateFormulationsInterderivable =
  (ApproximateRootExistence → ApproximateFundamentalTheorem) ×
  (ApproximateFundamentalTheorem → ApproximateRootExistence)

-- A positive, formal polynomial identity s*p + t*p′ = 1. This is stronger
-- data than the negative assertion "p has no repeated root". In particular,
-- the identity is not merely equality of evaluations at already known roots.
StronglySeparable : ∀ {n} → MonicPolynomial n → Type₀
StronglySeparable p = ∥ BezoutSeparability p ∥₁

PairwiseApartRoots : ∀ {n} → Vec ℂ n → Type₀
PairwiseApartRoots {n} roots = (i j : Fin n) → (i ≡ j → ⊥) →
  0ℝ <ℝ modulusℂ (lookup i roots -ℂ lookup j roots)

-- Native adaptation of Lubarsky--Richman, Theorem 4.4. Apartness is
-- positive metric separation, not merely unequal indices or unequal roots.
SeparableExactFactorization : ∀ {n} → MonicPolynomial n → Type₀
SeparableExactFactorization {n} p = ∥ Σ[ roots ∈ Vec ℂ n ]
  ((linearFactors roots ≡ p) × PairwiseApartRoots roots) ∥₁

StronglySeparableRootExistence : Type₀
StronglySeparableRootExistence = (n : ℕ) (p : MonicPolynomial (suc n)) →
  StronglySeparable p → ∥ ExactRootData p ∥₁

StronglySeparableFundamentalTheorem : Type₀
StronglySeparableFundamentalTheorem = (n : ℕ) (p : MonicPolynomial n) →
  StronglySeparable p → SeparableExactFactorization p

-- The certificate propagation obligation for finite exact deflation.
SeparableDeflation : Type₀
SeparableDeflation = (n : ℕ) (p : MonicPolynomial (suc n)) (r : ℂ) →
  evaluateMonic p r ≡ 0ℂ → BezoutSeparability p →
  BezoutSeparability (quotientMonic p r)
