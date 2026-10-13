module Cubical.Analysis.Complex.FundamentalTheorem.Formulations.ZeroSets where

-- Lubarsky--Richman 4.5--4.6: negative existence, quasifiniteness and
-- greatest lower bounds must not be replaced by located inhabited sets.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.FinData using (Fin)
open import Cubical.Data.Vec using (Vec; lookup)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty using (⊥)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁)
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open import Cubical.Analysis.Real.Base using (ℝ; rat)
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Order.Base using (_≤ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Modulus.Base using (modulusℂ)
open import Cubical.Analysis.Complex.Polynomial.Monic

IsPolynomialRoot : ∀ {n} → MonicPolynomial n → ℂ → Type₀
IsPolynomialRoot p z = evaluateMonic p z ≡ 0ℂ

RootQuasiApproximation : ∀ {n} → MonicPolynomial n → ℚ₊ → Vec ℂ n → Type₀
RootQuasiApproximation {n} p ε centers =
    ((i : Fin n) →
      ((Σ[ z ∈ ℂ ] (IsPolynomialRoot p z ×
        (modulusℂ (z -ℂ lookup i centers) <ℝ rat (fst ε)))) → ⊥) → ⊥) ×
    ((z : ℂ) → IsPolynomialRoot p z →
      ∥ Σ[ i ∈ Fin n ] (modulusℂ (z -ℂ lookup i centers) <ℝ rat (fst ε)) ∥₁)

QuasifiniteZeroSetTheorem : Type₀
QuasifiniteZeroSetTheorem = (n : ℕ) (p : MonicPolynomial (suc n)) (ε : ℚ₊) →
  ∥ Σ[ centers ∈ Vec ℂ (suc n) ] RootQuasiApproximation p ε centers ∥₁

RootDistanceGLB : ∀ {n} → MonicPolynomial n → ℂ → ℝ → Type₀
RootDistanceGLB p z d = (0ℝ ≤ℝ d) ×
  ((w : ℂ) → IsPolynomialRoot p w → d ≤ℝ modulusℂ (z -ℂ w)) ×
  ((b : ℝ) → ((w : ℂ) → IsPolynomialRoot p w → b ≤ℝ modulusℂ (z -ℂ w)) → b ≤ℝ d)

-- An actual native real GLB. Its construction needs justification for our
-- real carrier; the source paper's completeness cannot simply be imported.
-- There is NO near-minimizing root in this output.
QuasilocatedZeroSetTheorem : Type₀
QuasilocatedZeroSetTheorem = (n : ℕ) (p : MonicPolynomial (suc n)) (z : ℂ) →
  Σ[ d ∈ ℝ ] RootDistanceGLB p z d

-- Stronger, deliberately separate target: a located zero set supplies a
-- truncated near-minimizing ACTUAL root at every tolerance. This is not the
-- quasidistance claim above and is not claimed by the survey's weak FTA.
LocatedZeroSetTheorem : Type₀
LocatedZeroSetTheorem = (n : ℕ) (p : MonicPolynomial (suc n)) (z : ℂ) →
  Σ[ d ∈ ℝ ] (RootDistanceGLB p z d ×
    ((r : ℝ) → d <ℝ r → ∥ Σ[ w ∈ ℂ ]
      (IsPolynomialRoot p w × (modulusℂ (z -ℂ w) <ℝ r)) ∥₁))
