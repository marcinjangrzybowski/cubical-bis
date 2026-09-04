module Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Laws where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Negation
open import Cubical.Analysis.Real.Algebra.AdditiveGroup using (negInvol)
open import Cubical.Analysis.Real.Calculus.Derivative.Base
open import Cubical.Analysis.Real.Calculus.Derivative.Algebra
open import
  Cubical.Analysis.Real.Series.PowerSeries.Trigonometric.Entire


IsSecondDerivative :
  (function first-derivative second-derivative : ℝ → ℝ) → Type₀
IsSecondDerivative function first-derivative second-derivative =
  IsDerivative function first-derivative
  × IsDerivative first-derivative second-derivative


negativeSinℝHasDerivative :
  IsDerivative (λ x → - sinℝ x) (λ x → - cosℝ x)
negativeSinℝHasDerivative =
  negHasDerivative sinℝ cosℝ sinℝHasDerivative


negativeCosℝHasDerivative :
  IsDerivative (λ x → - cosℝ x) sinℝ
negativeCosℝHasDerivative =
  subst
    (IsDerivative (λ x → - cosℝ x))
    (funExt (λ x → negInvol (sinℝ x)))
    (negHasDerivative
      cosℝ (λ x → - sinℝ x) cosℝHasDerivative)


sinℝHasSecondDerivativeNegativeSelf :
  IsSecondDerivative sinℝ cosℝ (λ x → - sinℝ x)
sinℝHasSecondDerivativeNegativeSelf =
  sinℝHasDerivative , cosℝHasDerivative


cosℝHasSecondDerivativeNegativeSelf :
  IsSecondDerivative
    cosℝ (λ x → - sinℝ x) (λ x → - cosℝ x)
cosℝHasSecondDerivativeNegativeSelf =
  cosℝHasDerivative , negativeSinℝHasDerivative
