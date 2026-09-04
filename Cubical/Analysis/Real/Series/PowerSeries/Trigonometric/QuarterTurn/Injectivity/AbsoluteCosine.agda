module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.AbsoluteCosine where

open import Cubical.Foundations.Prelude

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.AbsoluteValue
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.AdditiveGroup using (negInvol)
open import Cubical.Analysis.Real.Order.AbsoluteValue
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Addition
open import Cubical.Analysis.Real.Order.Strict.Located
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Pi.Characterization
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.QuarterTurn.Injectivity.AbsoluteCosine.Core


opaque
  characterizedCosine-positive-inside : ∀ quarter →
    IsFirstPositiveCosineZero quarter →
    ∀ x → (- quarter) <ℝ x → x <ℝ quarter →
    0ℝ <ℝ cosℝ x
  characterizedCosine-positive-inside
      quarter characterization x negative-quarter<x x<quarter =
    subst (0ℝ <ℝ_)
      (cosℝ-absolute x)
      (firstPositiveCosineZero-positive-before
        characterization
        (absℝ x)
        (absNonnegative x)
        absolute<quarter)
    where
    negative-x<quarter : (- x) <ℝ quarter
    negative-x<quarter =
      subst ((- x) <ℝ_)
        (negInvol quarter)
        (<ℝ-neg (- quarter) x negative-quarter<x)

    absolute<quarter : absℝ x <ℝ quarter
    absolute<quarter =
      subst (_<ℝ quarter)
        (sym (absAsMax x))
        (maxStrictUpper x (- x) quarter
          x<quarter negative-x<quarter)
