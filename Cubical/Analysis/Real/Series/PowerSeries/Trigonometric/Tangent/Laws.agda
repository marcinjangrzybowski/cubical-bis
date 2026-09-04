module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent.Laws where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Sigma

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Algebra.Inverse.Signed
open import Cubical.Analysis.Real.Order.Apartness
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Tangent

opaque
  cosℝ-mul-tanℝ : ∀ point →
    cosℝ (fst point) · tanℝ point ≡ sinℝ (fst point)
  cosℝ-mul-tanℝ point =
    mulComm (cosℝ (fst point)) (tanℝ point)
    ∙ tanℝ-mul-cosℝ point


opaque
  cosℝ-mul-secℝ : ∀ point →
    cosℝ (fst point) · secℝ point ≡ 1ℝ
  cosℝ-mul-secℝ point =
    mulComm (cosℝ (fst point)) (secℝ point)
    ∙ secℝ-mul-cosℝ point
