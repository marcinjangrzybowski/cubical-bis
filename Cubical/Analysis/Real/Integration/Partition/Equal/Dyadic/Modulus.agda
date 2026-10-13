module Cubical.Analysis.Real.Integration.Partition.Equal.Dyadic.Modulus where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (invEq)
open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Inverse
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.AdditiveGroup
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Order.Strict.Slack
open import Cubical.Analysis.Real.Order.Strict.Multiplication
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Series.Geometric.Rational
open import Cubical.Analysis.Real.Integration.Partition.Mesh
open import Cubical.Analysis.Real.Integration.Partition.Equal.Dyadic

-- Unlike radiuswise vanishing mesh, this explicit index can be composed
-- with a supplied continuity modulus to build a native Cauchy witness.
dyadicMeshModulus : ℚ₊ → ℚ₊ → ℕ
dyadicMeshModulus bound δ = rationalGeometricModulus (δ ₊／₊ bound)

private
  halfNonnegative : 0 ℚ.≤ halfℚ
  halfNonnegative = ℚ.<Weaken≤ 0 halfℚ (snd (two₊ ⁻¹₊))

opaque
  dyadicRealNonnegative : ∀ n → 0ℝ ≤ℝ dyadicReal n
  dyadicRealNonnegative n = subst (0ℝ ≤ℝ_) (sym (pow-rat halfℚ n))
    (invEq (rat≤rat≃ 0 (powℚ halfℚ n))
      (rationalGeometricPowerNonnegative halfℚ halfNonnegative n))

  dyadicMeshModulusWorks : ∀ a b (a≤b : a ≤ℝ b) (bound δ : ℚ₊) →
    b - a ≤ℝ rat (fst bound) → ∀ n → dyadicMeshModulus bound δ ℕ.≤ n →
    HasMeshBelow (dyadicEqualPartition a b a≤b n) δ
  dyadicMeshModulusWorks a b a≤b bound δ length≤bound n large i =
    subst (_<ℝ rat (fst δ)) (sym (dyadicEqualPartition-width a b a≤b n i))
      (≤<ℝ-trans ((b - a) · dyadicReal n) (rat (fst bound) · dyadicReal n)
        (rat (fst δ))
        (mulPres≤R-0≤ (b - a) (rat (fst bound)) (dyadicReal n)
          (dyadicRealNonnegative n) length≤bound)
        (subst ((rat (fst bound) · dyadicReal n) <ℝ_)
          (mul-rat (fst bound) (fst (δ ₊／₊ bound)) ∙ cong rat (·／ bound δ))
          (mulPres<PosL (dyadicReal n) (rat (fst (δ ₊／₊ bound)))
            (rat (fst bound)) (positiveSlack bound)
            (subst (_<ℝ rat (fst (δ ₊／₊ bound))) (sym (pow-rat halfℚ n))
              (<ℚ→<ℝ (powℚ halfℚ n) (fst (δ ₊／₊ bound))
                (rationalGeometricPowerSmall halfℚ halfNonnegative (ℚ.isRefl≤ halfℚ)
                  (δ ₊／₊ bound) n large))))))
