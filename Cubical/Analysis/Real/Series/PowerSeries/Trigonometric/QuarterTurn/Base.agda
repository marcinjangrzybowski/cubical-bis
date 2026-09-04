module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ)
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire


IsPositiveQuarterTurn : ℝ → Type₀
IsPositiveQuarterTurn quarter =
  (cosℝ quarter ≡ 0ℝ) ×
  (sinℝ quarter ≡ 1ℝ)


isPropIsPositiveQuarterTurn : ∀ quarter →
  isProp (IsPositiveQuarterTurn quarter)
isPropIsPositiveQuarterTurn quarter =
  isProp×
    (isSetℝ (cosℝ quarter) 0ℝ)
    (isSetℝ (sinℝ quarter) 1ℝ)


quarterTurnCosineZero : ∀ {quarter} →
  IsPositiveQuarterTurn quarter →
  cosℝ quarter ≡ 0ℝ
quarterTurnCosineZero = fst


quarterTurnSineOne : ∀ {quarter} →
  IsPositiveQuarterTurn quarter →
  sinℝ quarter ≡ 1ℝ
quarterTurnSineOne = snd


halfTurn : ℝ → ℝ
halfTurn quarter = quarter + quarter


halfTurn-equation : ∀ quarter →
  halfTurn quarter ≡ quarter + quarter
halfTurn-equation quarter = refl


fullTurn : ℝ → ℝ
fullTurn quarter = halfTurn quarter + halfTurn quarter


fullTurn-equation : ∀ quarter →
  fullTurn quarter ≡
    halfTurn quarter + halfTurn quarter
fullTurn-equation quarter = refl
