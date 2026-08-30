module Cubical.Analysis.Real.Series.PowerSeries.Bounds where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals.Base
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Functions.Powers
open import Cubical.Analysis.Real.Functions.Powers.Order
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Real.Order.Strict.Rational
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Series.Base
open import Cubical.Analysis.Real.Series.Operations
open import Cubical.Analysis.Real.Series.Geometric.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Base

open PositiveRationals using (ℚ₊)


coefficientGeometricMajorant : ℚ₊ → ℚ₊ → RealSequence
coefficientGeometricMajorant bound radius =
  scaleSeries
    (rat (fst bound))
    (geometricTerms (rat (fst radius)))


private
  positiveRationalNonnegative : ∀ q →
    0ℝ ≤ℝ rat (fst q)
  positiveRationalNonnegative q =
    <ℝ-weaken 0ℝ (rat (fst q))
      (<ℚ→<ℝ 0 (fst q) (snd q))


powerSeriesTermAbsBound : ∀ bound radius coefficients x →
  CoefficientAbsBound bound coefficients →
  absℝ x ≤ℝ rat (fst radius) →
  ∀ n →
  absℝ (powerSeriesTerms coefficients x n) ≤ℝ
  coefficientGeometricMajorant bound radius n
powerSeriesTermAbsBound bound radius coefficients x
    coefficients-bounded absx≤radius n =
  subst
    (_≤ℝ coefficientGeometricMajorant bound radius n)
    (sym absoluteTermPath)
    productBound
  where
  absoluteTermPath :
    absℝ (powerSeriesTerms coefficients x n) ≡
    absℝ (coefficients n) · powℝ (absℝ x) n
  absoluteTermPath =
    absMul (coefficients n) (powℝ x n)
    ∙ cong (absℝ (coefficients n) ·_) (absPow x n)

  powerBound :
    powℝ (absℝ x) n ≤ℝ
    powℝ (rat (fst radius)) n
  powerBound =
    powMono n (absNonnegative x) absx≤radius

  productBound :
    absℝ (coefficients n) · powℝ (absℝ x) n ≤ℝ
    coefficientGeometricMajorant bound radius n
  productBound =
    mulPres≤
      (absℝ (coefficients n))
      (rat (fst bound))
      (powℝ (absℝ x) n)
      (powℝ (rat (fst radius)) n)
      (positiveRationalNonnegative bound)
      (powNonnegative (absℝ x) n (absNonnegative x))
      (coefficients-bounded n)
      powerBound
