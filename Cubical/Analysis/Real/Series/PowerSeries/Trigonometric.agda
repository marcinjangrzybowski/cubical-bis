module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric where

open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Coefficients public
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Convergence public
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.HigherDerivative public
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.HigherEntire public
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire public
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Parity public
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Laws public
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Bounds public
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pythagorean public
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.SharpBounds public
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Estimates.UniformDerivative public
  using (sinℝHasUniformDerivative; cosℝHasUniformDerivative)
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Estimates.NonExpanding public
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Estimates.AdditionDerived public
  using (sinℝ-sub; cosℝ-sub; sinℝ-difference-expansion; cosℝ-difference-expansion)
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Addition public
  hiding
    ( sinePowerSeriesIsAbsolutelyCauchy
    ; cosinePowerSeriesIsAbsolutelyCauchy
    )
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Identities public
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Identities.Products public
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Identities.Squares public
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Integrals public
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent public
  hiding
    ( cosℝ-zero-for-tangent
    ; sinℝ-zero-for-tangent
    ; cosineAtZeroApart
    ; tanℝ-definingEquation
    ; secℝ-definingEquation
    ; divideZeroOnTangentDomain
    ; divideOnTangentDomainPresNumerator
    )
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Laws public
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.AtZero public
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Parity public
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Identities public
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Addition public
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn public
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi public
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Estimates.SmallAngle public
