module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Bishop.CosineAtZero where

open import Cubical.Foundations.Prelude

open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ)
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire


opaque
  bishopCosineAtZero : cosℝ 0ℝ ≡ 1ℝ
  bishopCosineAtZero = cosℝ-zero
