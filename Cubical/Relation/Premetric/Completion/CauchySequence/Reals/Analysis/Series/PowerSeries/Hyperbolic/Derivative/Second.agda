module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Derivative.Second where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma using (_×_ ; _,_)

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Derivative.Sinh
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Derivative.Cosh


IsSecondDerivative :
  (function first-derivative second-derivative :
    Real.ℝ → Real.ℝ) → Type₀
IsSecondDerivative function first-derivative second-derivative =
  IsDerivative function first-derivative ×
  IsDerivative first-derivative second-derivative


sinhℝHasSecondDerivativeSelf :
  IsSecondDerivative sinhℝ coshℝ sinhℝ
sinhℝHasSecondDerivativeSelf =
  sinhℝHasDerivativeCoshℝ , coshℝHasDerivativeSinhℝ


coshℝHasSecondDerivativeSelf :
  IsSecondDerivative coshℝ sinhℝ coshℝ
coshℝHasSecondDerivativeSelf =
  coshℝHasDerivativeSinhℝ , sinhℝHasDerivativeCoshℝ
