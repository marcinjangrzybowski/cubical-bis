module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.LocallyUniform.Smooth where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Sigma

open import Cubical.Relation.Premetric.Mappings

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.LocallyUniform
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.LocallyUniform.Continuity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.LocallyUniform.Derivative


iteratedFormalDerivative : RealSequence → ℕ → RealSequence
iteratedFormalDerivative coefficients zero = coefficients
iteratedFormalDerivative coefficients (suc order) =
  formalDerivative (iteratedFormalDerivative coefficients order)


iteratedFormalDerivative-zero : ∀ coefficients →
  iteratedFormalDerivative coefficients zero ≡ coefficients
iteratedFormalDerivative-zero coefficients = refl


iteratedFormalDerivative-suc : ∀ coefficients order →
  iteratedFormalDerivative coefficients (suc order) ≡
  formalDerivative (iteratedFormalDerivative coefficients order)
iteratedFormalDerivative-suc coefficients order = refl


-- Smoothness data retains the radiuswise uniform information at every formal
-- derivative, rather than forgetting it after proving an ordinary derivative.
-- This is the form needed for repeated differentiation and termwise
-- integration.  It is intentionally explicit countable proof data: this
-- definition does not turn `∀ n → ∥ witness n ∥₁` into chosen witnesses.

LocallyUniformSmoothPowerSeries : RealSequence → Type₀
LocallyUniformSmoothPowerSeries coefficients =
  (∀ order →
    LocallyUniformPowerSeries
      (iteratedFormalDerivative coefficients order))
  ×
  (∀ order →
    LocallyUniformPowerSeriesDifferenceFactor
      (iteratedFormalDerivative coefficients order))


isPropLocallyUniformSmoothPowerSeries : ∀ coefficients →
  isProp (LocallyUniformSmoothPowerSeries coefficients)
isPropLocallyUniformSmoothPowerSeries coefficients =
  isProp×
    (isPropΠ λ order →
      isPropLocallyUniformPowerSeries
        (iteratedFormalDerivative coefficients order))
    (isPropΠ λ order →
      isPropLocallyUniformPowerSeriesDifferenceFactor
        (iteratedFormalDerivative coefficients order))


locallyUniformSmoothPowerSeriesValue :
  ∀ coefficients →
  LocallyUniformSmoothPowerSeries coefficients →
  ℕ → Real.ℝ → Real.ℝ
locallyUniformSmoothPowerSeriesValue coefficients smooth order =
  locallyUniformPowerSeriesValue
    (iteratedFormalDerivative coefficients order)
    (fst smooth order)


locallyUniformSmoothPowerSeriesValueIsContinuous :
  ∀ coefficients smooth order →
  isContinuous
    (snd Real.ℝPremetricSpace)
    (locallyUniformSmoothPowerSeriesValue
      coefficients smooth order)
    (snd Real.ℝPremetricSpace)
locallyUniformSmoothPowerSeriesValueIsContinuous
  coefficients smooth order =
  locallyUniformPowerSeriesValueIsContinuous
    (iteratedFormalDerivative coefficients order)
    (fst smooth order)


-- Every level in the tower differentiates to the next canonical whole-line
-- value.  No equality transport between separately chosen sums is exposed;
-- that work is centralized in the locally uniform derivative theorem.

locallyUniformSmoothPowerSeriesHasNextDerivative :
  ∀ coefficients smooth order →
  IsDerivative
    (locallyUniformSmoothPowerSeriesValue
      coefficients smooth order)
    (locallyUniformSmoothPowerSeriesValue
      coefficients smooth (suc order))
locallyUniformSmoothPowerSeriesHasNextDerivative
  coefficients smooth order =
  locallyUniformPowerSeriesHasFormalDerivative
    (iteratedFormalDerivative coefficients order)
    (fst smooth order)
    (fst smooth (suc order))
    (snd smooth order)
