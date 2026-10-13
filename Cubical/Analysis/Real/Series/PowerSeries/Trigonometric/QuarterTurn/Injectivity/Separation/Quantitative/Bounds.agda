module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Quantitative.Bounds where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveHalvesℚ
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Estimates.SmallAngle
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.LowerBound
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.Separation.Quantitative.Algebra

opaque
  rationalHalfSquareBound : ∀ (q : ℚ₊) → rat (fst q) ≤ℝ 1ℝ →
    rat (fst (squareRadius (halfRadius q))) ≤ℝ quarterTurnSineSeparationBound q
  rationalHalfSquareBound = rationalSquareBoundFor sinℝ sinℝ-rationalHalfLowerBound
