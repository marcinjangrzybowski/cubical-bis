module Cubical.Analysis.Complex.FundamentalTheorem.BoundedRoots where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Analysis.Real.Base using (ℝ; rat)
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ)
open import Cubical.Analysis.Real.Order.Base using (≤ℝ-trans)
open import Cubical.Analysis.Real.Order.Strict.Properties using (<ℝ-weaken)
open import Cubical.Analysis.Real.Order.Archimedean
open import Cubical.Analysis.Complex.Norm using (normℂ)
open import Cubical.Analysis.Complex.Polynomial.Monic.Coercivity
open import Cubical.Analysis.Complex.FundamentalTheorem.Formulations.LocalRoots
  using (BoundedApproximateRoots)

-- A single Archimedean bound is chosen inside the truncated conclusion.
-- It bounds every small-residual point simultaneously; no sequence of
-- approximate roots or radius-indexed choices is extracted.
boundedApproximateRoots : BoundedApproximateRoots
boundedApproximateRoots n p = PT.map
  (λ (k , upper) → naturalBound k , λ z small →
    ≤ℝ-trans (normℂ z) (radius + radius) (rat (naturalRational k))
      (smallResidual-normBound p z small)
      (<ℝ-weaken (radius + radius) (rat (naturalRational k)) upper))
  (∃naturalUpperBound (radius + radius))
  where
  radius : ℝ
  radius = monicCoerciveRadius p + 1ℝ
