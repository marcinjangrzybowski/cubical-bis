module Cubical.Analysis.Complex.FundamentalTheorem.Formulations.SpecialCases where

-- Further exact formulations mentioned in the survey: the nonmonic scope
-- of Ruitenburg 3.13 and the one-real-parameter setting of 3.16. These are
-- native statement targets, not imports of the paper's real/complex carrier.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.FinData using (Fin)
open import Cubical.Data.Vec using (Vec; lookup; map; tabulate)
open import Cubical.Data.List using (List; []; _∷_)
import Cubical.Data.List as List
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit)
open import Cubical.Data.Rationals.Base using (ℚ)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁)
open import Cubical.Analysis.Real.Base using (ℝ)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Inverse using (ComplexNonzero; inverseℂ)
open import Cubical.Analysis.Complex.Polynomial.Base
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Basic
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Presented

ListCoefficientPresentations : List ℂ → Type₀
ListCoefficientPresentations [] = Unit
ListCoefficientPresentations (a ∷ p) = RationalPresentationℂ a × ListCoefficientPresentations p

-- An invertible coefficient of ANY positive power suffices. In particular,
-- the last formal coefficient need not be known invertible. Names form a
-- finite input package; the output retains a name for the exact root.
PresentedNonmonicRootExistence : Type₀
PresentedNonmonicRootExistence = (p : List ℂ) (k : ℕ) →
  ListCoefficientPresentations p → ComplexNonzero (polynomialCoefficientℂ p (suc k)) →
  ∥ Σ[ z ∈ ℂ ] ((evaluatePolynomialℂ p z ≡ 0ℂ) × RationalPresentationℂ z) ∥₁

-- Algebraicity over Q is witnessed by a monic rational polynomial. This
-- predicate does not presuppose a discrete implementation of algebraic
-- numbers, nor an equivalence with such an implementation.
IsAlgebraicComplex : ℂ → Type₀
IsAlgebraicComplex z = ∥ Σ[ n ∈ ℕ ] Σ[ p ∈ Vec ℚ (suc n) ]
  evaluateMonic (map fromℚ p) z ≡ 0ℂ ∥₁

AlgebraicComplex : Type₀
AlgebraicComplex = Σ[ z ∈ ℂ ] IsAlgebraicComplex z

AlgebraicRationalFunction : Type₀
AlgebraicRationalFunction = List AlgebraicComplex × List AlgebraicComplex

algebraicPolynomialValue : List AlgebraicComplex → ℝ → ℂ
algebraicPolynomialValue p r = evaluatePolynomialℂ (List.map fst p) (fromℝ r)

RationalFunctionDefinedAt : AlgebraicRationalFunction → ℝ → Type₀
RationalFunctionDefinedAt f r = ComplexNonzero (algebraicPolynomialValue (snd f) r)

opaque
  algebraicRationalFunctionValue : (f : AlgebraicRationalFunction) (r : ℝ) →
    RationalFunctionDefinedAt f r → ℂ
  algebraicRationalFunctionValue f r defined = algebraicPolynomialValue (fst f) r ·ℂ
    inverseℂ (algebraicPolynomialValue (snd f) r) defined

-- Every coefficient is a rational function of the SAME native real r,
-- with algebraic complex coefficients and a denominator apart from zero.
-- This does not cover arbitrary dependence on two real coordinates, and
-- it does not assume a rational Cauchy presentation of r.
OneRealParameterFundamentalTheorem : Type₀
OneRealParameterFundamentalTheorem = (n : ℕ) (r : ℝ)
  (functions : Vec AlgebraicRationalFunction n)
  (defined : (i : Fin n) → RationalFunctionDefinedAt (lookup i functions) r) →
  ExactFactorization (tabulate (λ i → algebraicRationalFunctionValue (lookup i functions) r (defined i)))
