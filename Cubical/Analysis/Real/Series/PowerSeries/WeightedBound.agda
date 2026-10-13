module Cubical.Analysis.Real.Series.PowerSeries.WeightedBound where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.CommRing
open import Cubical.Analysis.Real.Algebra.Nonnegative
open import Cubical.Analysis.Real.Algebra.Inverse.Positive
open import Cubical.Analysis.Real.Algebra.Inverse.Order
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Order.Strict.Multiplication
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Functions.Powers.Order
open import Cubical.Analysis.Real.Functions.Powers.Ring
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Operations
open import Cubical.Analysis.Real.Series.Absolute
open import Cubical.Analysis.Real.Series.Geometric.Real

open PositiveRationals using (ℚ₊)

private
  module WeightedAlgebra {ℓ} (R : CommRing ℓ) where
    open CommRingStr (snd R) renaming (_·_ to _·r_)
    open Exponentiation R
    private module C = CommRingTheory R

    opaque
      cancelPowerWeight : ∀ a outer inverse inner n → outer ·r inverse ≡ 1r →
        (a ·r (outer ^ n)) ·r ((inner ·r inverse) ^ n) ≡ a ·r (inner ^ n)
      cancelPowerWeight a outer inverse inner n unit = sym (·Assoc a (outer ^ n) ((inner ·r inverse) ^ n))
        ∙ cong (a ·r_) (sym (^-ldist-· outer (inner ·r inverse) n)
          ∙ cong (_^ n) (C.·CommAssocl outer inner inverse ∙ cong (inner ·r_) unit ∙ ·IdR inner))

  module A = WeightedAlgebra ℝCommRing

-- A weighted coefficient bound at one positive radius gives a geometric
-- native majorant at every strictly smaller nonnegative radius. No
-- monotone-convergence principle or choice of pointwise tails is used.
module _ (inner outer : ℝ) (nonnegative : 0ℝ ≤ℝ inner) (strict : inner <ℝ outer) where
  private
    positive : 0ℝ <ℝ outer
    positive = ≤<ℝ-trans 0ℝ inner outer nonnegative strict

    inverse : ℝ
    inverse = positiveReciprocal outer positive

    inversePositive : 0ℝ <ℝ inverse
    inversePositive = positiveReciprocalPositive outer positive

  weightedBoundRatio : ℝ
  weightedBoundRatio = inner · inverse

  opaque
    weightedBoundRatioNonnegative : 0ℝ ≤ℝ weightedBoundRatio
    weightedBoundRatioNonnegative = isNonnegative→0≤ weightedBoundRatio
      (mulPresIsNonnegative inner inverse (0≤→isNonnegative inner nonnegative)
        (0≤→isNonnegative inverse (<ℝ-weaken 0ℝ inverse inversePositive)))

    weightedBoundRatioContraction : absℝ weightedBoundRatio <ℝ 1ℝ
    weightedBoundRatioContraction = subst2 _<ℝ_
      (sym (absOfNonnegative weightedBoundRatio weightedBoundRatioNonnegative))
      (positiveReciprocalLaw outer positive)
      (mulPres<PosR inner outer inverse inversePositive strict)

  weightedBoundMajorant : ℚ₊ → RealSequence
  weightedBoundMajorant bound n = rat (fst bound) · powℝ weightedBoundRatio n

  weightedBoundMajorantIsCauchy : ∀ bound → IsCauchySeries (weightedBoundMajorant bound)
  weightedBoundMajorantIsCauchy bound = rationalScaleSeriesIsCauchy (fst bound)
    (λ n → powℝ weightedBoundRatio n)
    (realGeometricSeriesIsCauchy weightedBoundRatio weightedBoundRatioContraction)

  opaque
    weightedCoefficientTermBound : ∀ coefficient bound n →
      coefficient · powℝ outer n ≤ℝ rat (fst bound) →
      coefficient · powℝ inner n ≤ℝ weightedBoundMajorant bound n
    weightedCoefficientTermBound coefficient bound n bounded = subst
      (_≤ℝ weightedBoundMajorant bound n)
      (cong₂ _·_ (cong (coefficient ·_) (powℝ-as-ringPower outer n)) (powℝ-as-ringPower weightedBoundRatio n)
        ∙ A.cancelPowerWeight coefficient outer inverse inner n (positiveReciprocalLaw outer positive)
        ∙ cong (coefficient ·_) (sym (powℝ-as-ringPower inner n)))
      (mulPres≤R-0≤ (coefficient · powℝ outer n) (rat (fst bound))
        (powℝ weightedBoundRatio n) (powNonnegative weightedBoundRatio n weightedBoundRatioNonnegative) bounded)
