module Cubical.Analysis.Real.Series.PowerSeries.Uniform where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Rationals.Base as ℚ
import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Domain.Radius
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Uniform
open import Cubical.Analysis.Real.Series.Geometric.Rational
open import Cubical.Analysis.Real.Series.PowerSeries.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Bounds
open import Cubical.Analysis.Real.Series.PowerSeries.Convergence

open PositiveRationals using (ℚ₊)


ClosedRationalRadius : ℚ₊ → Type₀
ClosedRationalRadius radius =
  ClosedAbsRadius (rat (fst radius))


powerSeriesOnClosedRadius :
  RealSequence → (radius : ℚ₊) →
  ClosedRationalRadius radius → RealSequence
powerSeriesOnClosedRadius coefficients radius point =
  powerSeriesTerms coefficients (fst point)


powerSeriesUniformlyCauchyByHalfMajorant :
  ∀ bound radius coefficients →
  CoefficientAbsBound bound coefficients →
  fst radius ℚ.≤ halfℚ →
  UniformlyCauchySeries
    (ClosedRationalRadius radius)
    (powerSeriesOnClosedRadius coefficients radius)
powerSeriesUniformlyCauchyByHalfMajorant
    bound radius coefficients coefficients-bounded radius≤half =
  uniformlyDominatedSeriesIsUniformlyCauchy
    (powerSeriesOnClosedRadius coefficients radius)
    (coefficientGeometricMajorant bound radius)
    (λ point →
      powerSeriesTermAbsBound
        bound radius coefficients (fst point)
        coefficients-bounded (snd point))
    (coefficientGeometricMajorantIsCauchy
      bound radius radius≤half)


powerSeriesClosedRadiusSummable :
  ∀ bound radius coefficients →
  (coefficients-bounded : CoefficientAbsBound bound coefficients) →
  (radius≤half : fst radius ℚ.≤ halfℚ) →
  ∀ point → PowerSeriesSummableAt coefficients (fst point)
powerSeriesClosedRadiusSummable
    bound radius coefficients coefficients-bounded radius≤half point =
  uniformlyCauchySeriesSummableAt
    (powerSeriesUniformlyCauchyByHalfMajorant
      bound radius coefficients coefficients-bounded radius≤half)
    point


powerSeriesClosedRadiusValue :
  ∀ bound radius coefficients →
  CoefficientAbsBound bound coefficients →
  fst radius ℚ.≤ halfℚ →
  ClosedRationalRadius radius → ℝ
powerSeriesClosedRadiusValue
    bound radius coefficients coefficients-bounded radius≤half =
  uniformSeriesValue
    (powerSeriesOnClosedRadius coefficients radius)
    (powerSeriesUniformlyCauchyByHalfMajorant
      bound radius coefficients coefficients-bounded radius≤half)


private
  constantOnClosedRadiusIsContinuous :
    (radius : ℚ₊) (coefficient : ℝ) →
    isContinuous
      (ClosedAbsRadiusPremetricSpace (rat (fst radius)) .snd)
      (λ _ → coefficient)
      (ℝPremetricSpace .snd)
  constantOnClosedRadiusIsContinuous radius coefficient point
    .IsContinuousAt.pres≈ ε =
    ∣ ε , (λ _ _ → refl∼ coefficient ε) ∣₁

  powerOnClosedRadiusIsContinuous :
    (radius : ℚ₊) (n : ℕ) →
    isContinuous
      (ClosedAbsRadiusPremetricSpace (rat (fst radius)) .snd)
      (λ point → powℝ (fst point) n)
      (ℝPremetricSpace .snd)
  powerOnClosedRadiusIsContinuous radius n point
    .IsContinuousAt.pres≈ ε =
    PT.map
      (λ where
        (δ , near) →
          δ , λ other point≈other →
            near (fst other) point≈other)
      (pow-isContinuous n (fst point) .IsContinuousAt.pres≈ ε)


powerSeriesTermOnClosedRadiusIsContinuous :
  (coefficients : RealSequence) (radius : ℚ₊) (n : ℕ) →
  isContinuous
    (ClosedAbsRadiusPremetricSpace (rat (fst radius)) .snd)
    (λ point →
      powerSeriesOnClosedRadius coefficients radius point n)
    (ℝPremetricSpace .snd)
powerSeriesTermOnClosedRadiusIsContinuous
    coefficients radius n =
  mulOfContinuousIsContinuous
    (ClosedAbsRadiusPremetricSpace (rat (fst radius)) .snd)
    (λ _ → coefficients n)
    (λ point → powℝ (fst point) n)
    (constantOnClosedRadiusIsContinuous
      radius (coefficients n))
    (powerOnClosedRadiusIsContinuous radius n)


powerSeriesClosedRadiusValueIsContinuous :
  ∀ bound radius coefficients →
  (coefficients-bounded : CoefficientAbsBound bound coefficients) →
  (radius≤half : fst radius ℚ.≤ halfℚ) →
  isContinuous
    (ClosedAbsRadiusPremetricSpace (rat (fst radius)) .snd)
    (powerSeriesClosedRadiusValue
      bound radius coefficients coefficients-bounded radius≤half)
    (ℝPremetricSpace .snd)
powerSeriesClosedRadiusValueIsContinuous
    bound radius coefficients coefficients-bounded radius≤half =
  uniformSeriesValueIsContinuous
    (ClosedAbsRadiusPremetricSpace (rat (fst radius)) .snd)
    (powerSeriesOnClosedRadius coefficients radius)
    (powerSeriesUniformlyCauchyByHalfMajorant
      bound radius coefficients coefficients-bounded radius≤half)
    (powerSeriesTermOnClosedRadiusIsContinuous coefficients radius)
