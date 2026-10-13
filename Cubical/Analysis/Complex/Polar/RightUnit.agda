module Cubical.Analysis.Complex.Polar.RightUnit where

open import Cubical.Foundations.Prelude
open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.AdditionLaws
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import Cubical.Analysis.Complex.Polar.Cis
open import Cubical.Analysis.Complex.Polar.RightUnit.Inverse
open import Cubical.Analysis.Complex.Polar.RightUnit.Reconstruction

module RightUnit (a b : ℝ) (positive : 0ℝ <ℝ a) (unit : a · a + b · b ≡ 1ℝ) where
  open RightUnitInverse a b positive unit public

  opaque
    reconstruct : cisℝ argument ≡ (a , b)
    reconstruct = reconstructUnit a b argument positive unit
      argument-above argument-below sine-argument
