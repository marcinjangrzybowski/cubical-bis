module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.LocallyUniform.Continuity where

open import Cubical.Foundations.Prelude

open import Cubical.Data.NatPlusOne
open import Cubical.Data.Rationals.Base

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.Relation.Premetric.Mappings

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Archimedean
  using
    ( NaturalBound ; ∃naturalBound
    ; naturalRational ; naturalPositive
    )
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Metric.Radius
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Metric.Radius.Continuity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Uniform
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.LocallyUniform


-- Local uniform convergence already supplies global continuity; the stronger
-- divided-difference hypothesis used for differentiation is unnecessary.
-- As in the derivative theorem, a strict natural radius is opened only into
-- a proposition-valued pointwise continuity statement.

locallyUniformPowerSeriesValueIsContinuous :
  ∀ coefficients
    (local : LocallyUniformPowerSeries coefficients) →
  isContinuous
    (snd Real.ℝPremetricSpace)
    (locallyUniformPowerSeriesValue coefficients local)
    (snd Real.ℝPremetricSpace)
locallyUniformPowerSeriesValueIsContinuous coefficients local x =
  PT.rec
    (isPropIsContinuousAt
      (snd Real.ℝPremetricSpace)
      (locallyUniformPowerSeriesValue coefficients local)
      (snd Real.ℝPremetricSpace) x)
    bounded-continuity
    (∃naturalBound x)
  where
  bounded-continuity : NaturalBound x →
    IsContinuousAt
      (snd Real.ℝPremetricSpace)
      (locallyUniformPowerSeriesValue coefficients local)
      (snd Real.ℝPremetricSpace) x
  bounded-continuity (n , interior) =
    closedAbsRadiusContinuousAtInteriorWithExtension
      (Real.ιℚ (naturalRational n))
      (powerSeriesUniformValueOnClosedRadius
        coefficients
        (Real.ιℚ (naturalRational n))
        (local radius))
      (locallyUniformPowerSeriesValue coefficients local)
      (powerSeriesUniformValueOnClosedRadiusIsContinuous
        coefficients
        (Real.ιℚ (naturalRational n))
        (local radius))
      (locallyUniformPowerSeriesValue-agreesOnRadius
        coefficients local radius)
      x interior
    where
    radius : ℚ₊
    radius = naturalRational n , naturalPositive n
