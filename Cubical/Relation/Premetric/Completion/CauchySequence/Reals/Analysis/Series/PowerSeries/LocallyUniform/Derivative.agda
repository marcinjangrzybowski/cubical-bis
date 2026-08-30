module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.LocallyUniform.Derivative where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.NatPlusOne
open import Cubical.Data.Rationals.Base

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
  using (<ℝ-weaken)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Archimedean
  using
    ( NaturalBound ; ∃naturalBound
    ; naturalRational ; naturalPositive
    )
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Metric.Radius
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Uniform
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Uniform
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Difference.Uniform
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Interior
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.LocallyUniform


private
  isPropDerivativeAt : ∀ function derivative-value x →
    isProp (IsDerivativeAt function derivative-value x)
  isPropDerivativeAt function derivative-value x =
    isPropΠ λ _ → squash₁


-- The divided-difference series is the genuinely useful third hypothesis
-- for termwise differentiation.  Keeping it explicit makes this theorem
-- applicable beyond a particular majorant criterion.

LocallyUniformPowerSeriesDifferenceFactor :
  RealSequence → Type₀
LocallyUniformPowerSeriesDifferenceFactor coefficients =
  (radius : ℚ₊) →
    PowerSeriesDifferenceFactorUniformlyCauchyOnRadius
      coefficients (Real.ιℚ (fst radius))


isPropLocallyUniformPowerSeriesDifferenceFactor : ∀ coefficients →
  isProp (LocallyUniformPowerSeriesDifferenceFactor coefficients)
isPropLocallyUniformPowerSeriesDifferenceFactor coefficients =
  isPropΠ λ radius →
    isPropUniformlyCauchySeries
      (ClosedAbsRadiusPair (Real.ιℚ (fst radius)))
      (powerSeriesDifferenceFactorOnClosedRadius
        coefficients (Real.ιℚ (fst radius)))


-- Global termwise differentiation requires no global selection of a radius.
-- At a point x, mere existence of a strict natural radius is eliminated
-- directly into IsDerivativeAt, which is a proposition.  The local result is
-- then transported from the uniform derivative sum to the canonical
-- whole-line derivative sum by uniqueness of series sums.

locallyUniformPowerSeriesHasFormalDerivative :
  ∀ coefficients →
  (local : LocallyUniformPowerSeries coefficients) →
  (derivative-local :
    LocallyUniformPowerSeries (formalDerivative coefficients)) →
  LocallyUniformPowerSeriesDifferenceFactor coefficients →
  IsDerivative
    (locallyUniformPowerSeriesValue coefficients local)
    (locallyUniformPowerSeriesValue
      (formalDerivative coefficients) derivative-local)
locallyUniformPowerSeriesHasFormalDerivative
  coefficients local derivative-local factor-local x =
  PT.rec
    (isPropDerivativeAt
      (locallyUniformPowerSeriesValue coefficients local)
      (locallyUniformPowerSeriesValue
        (formalDerivative coefficients) derivative-local x)
      x)
    bounded-derivative
    (∃naturalBound x)
  where
  bounded-derivative : NaturalBound x →
    IsDerivativeAt
      (locallyUniformPowerSeriesValue coefficients local)
      (locallyUniformPowerSeriesValue
        (formalDerivative coefficients) derivative-local x)
      x
  bounded-derivative (n , interior) =
    subst
      (λ derivative-value →
        IsDerivativeAt
          (locallyUniformPowerSeriesValue coefficients local)
          derivative-value x)
      (sym derivative-agreement)
      local-derivative
    where
    radius : ℚ₊
    radius = naturalRational n , naturalPositive n

    closed-point :
      ClosedAbsRadius (Real.ιℚ (fst radius))
    closed-point = x , <ℝ-weaken
      (Abs.absℝ x) (Real.ιℚ (fst radius)) interior

    local-derivative :
      IsDerivativeAt
        (locallyUniformPowerSeriesValue coefficients local)
        (powerSeriesUniformValueOnClosedRadius
          (formalDerivative coefficients)
          (Real.ιℚ (fst radius))
          (derivative-local radius)
          closed-point)
        x
    local-derivative =
      powerSeriesUniformValueHasFormalDerivativeAtInteriorWithExtension
        coefficients
        (Real.ιℚ (fst radius))
        (local radius)
        (derivative-local radius)
        (factor-local radius)
        (locallyUniformPowerSeriesValue coefficients local)
        (locallyUniformPowerSeriesValue-agreesOnRadius
          coefficients local radius)
        x interior

    derivative-agreement :
      locallyUniformPowerSeriesValue
        (formalDerivative coefficients) derivative-local x
        ≡
      powerSeriesUniformValueOnClosedRadius
        (formalDerivative coefficients)
        (Real.ιℚ (fst radius))
        (derivative-local radius)
        closed-point
    derivative-agreement =
      locallyUniformPowerSeriesValue-agreesOnRadius
        (formalDerivative coefficients)
        derivative-local radius closed-point
