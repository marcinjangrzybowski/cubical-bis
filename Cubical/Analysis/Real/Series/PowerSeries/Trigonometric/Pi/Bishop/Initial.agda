module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Bishop.Initial where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat using (zero; suc)

open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ; addIdL)
open import Cubical.Analysis.Real.Algebra.Addition using (_+_)
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ)
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Bishop.Iteration
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Bishop.CosineAtZero


opaque
  bishopPiHalfApproximation-one :
    bishopPiHalfApproximation (suc zero) ≡ 1ℝ
  bishopPiHalfApproximation-one =
    bishopPiHalfApproximation-step zero
    ∙ (cong₂ _+_
        bishopPiHalfApproximation-zero
        (cong cosℝ bishopPiHalfApproximation-zero))
    ∙ addIdL (cosℝ 0ℝ)
    ∙ bishopCosineAtZero
