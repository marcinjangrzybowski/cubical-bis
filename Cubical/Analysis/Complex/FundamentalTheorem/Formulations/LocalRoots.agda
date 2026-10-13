module Cubical.Analysis.Complex.FundamentalTheorem.Formulations.LocalRoots where

-- Intermediate targets in the preferred proof plan. These are ordinary
-- quantitative analytic hypotheses, not choice or convergence assumptions.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.FinData using (Fin)
open import Cubical.Data.Vec using (Vec; lookup)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁)
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open import Cubical.Analysis.Real.Base using (ℝ; rat)
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.AdditiveGroup using (_-_)
open import Cubical.Analysis.Real.Algebra.Multiplication using (_·_)
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ)
open import Cubical.Analysis.Real.Order.Base using (_≤ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Complex.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm using (normℂ)
open import Cubical.Analysis.Complex.Modulus.Base using (modulusℂ)
open import Cubical.Analysis.Complex.Metric
open import Cubical.Analysis.Complex.Contraction using (ComplexBall)
open import Cubical.Analysis.Complex.Polynomial.Monic
open import Cubical.Analysis.Complex.Polynomial.Differential.Monic
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.Presented

-- A divided-difference error estimate relative to one fixed derivative.
-- Together with an inverse and small correction it implies contraction of
-- z ↦ z - inverse*p(z); the conclusion below must construct its native limit.
NewtonErrorBound : ∀ {n} → MonicPolynomial n → ℂ → ℝ → ℝ → Type₀
NewtonErrorBound p center radius error = (z w : ℂ) →
  ComplexBall center radius z → ComplexBall center radius w →
  normℂ ((evaluateMonic p z -ℂ evaluateMonic p w) -ℂ
    derivativeMonic p center ·ℂ (z -ℂ w)) ≤ℝ error · normℂ (z -ℂ w)

LocalNewtonRootTheorem : Type₀
LocalNewtonRootTheorem = (n : ℕ) (p : MonicPolynomial n) (center inverse : ℂ)
  (radius error q : ℝ) →
  inverse ·ℂ derivativeMonic p center ≡ 1ℂ →
  0ℝ <ℝ radius → 0ℝ ≤ℝ error → 0ℝ ≤ℝ q → q <ℝ 1ℝ →
  normℂ inverse · error ≤ℝ q →
  normℂ (inverse ·ℂ evaluateMonic p center) ≤ℝ (1ℝ - q) · radius →
  NewtonErrorBound p center radius error →
  Σ[ root ∈ ℂ ] (ComplexBall center radius root × (evaluateMonic p root ≡ 0ℂ) ×
    ((z : ℂ) → ComplexBall center radius z → evaluateMonic p z ≡ 0ℂ → z ≡ root))

-- One finite bound, uniform over all points with small residual. This is
-- the coercivity lemma needed to use Bézout bounds at an approximate root.
BoundedApproximateRoots : Type₀
BoundedApproximateRoots = (n : ℕ) (p : MonicPolynomial (suc n)) →
  ∥ Σ[ bound ∈ ℚ₊ ] ((z : ℂ) → modulusℂ (evaluateMonic p z) <ℝ 1ℝ →
    normℂ z ≤ℝ rat (fst bound)) ∥₁

-- A finite Gaussian net controlling ALL sufficiently small-residual points,
-- rather than just one approximate zero. This is a quantitative target
-- suggested by the presented-coefficient algorithms; no root is extracted
-- from a net here. The centers themselves have small residual.
-- Inhabited by nearZeroNet in FundamentalTheorem.NearZeroNet. The proof
-- retains each small-residual point in an approximate factorization and
-- matches it to a sufficiently accurate Gaussian factorization.
NearZeroNetTheorem : Type₀
NearZeroNetTheorem = (n : ℕ) (p : MonicPolynomial (suc n)) (ε : ℚ₊) →
  ∥ Σ[ δ ∈ ℚ₊ ] Σ[ k ∈ ℕ ] Σ[ centers ∈ Vec GaussianRational (suc k) ]
    (((i : Fin (suc k)) → evaluateMonic p (gaussianℂ (lookup i centers)) ∼ℂ[ ε ] 0ℂ) ×
      ((z : ℂ) → evaluateMonic p z ∼ℂ[ δ ] 0ℂ →
        ∥ Σ[ i ∈ Fin (suc k) ] z ∼ℂ[ ε ] gaussianℂ (lookup i centers) ∥₁)) ∥₁
