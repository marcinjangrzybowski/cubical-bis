module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.LocallyUniform where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Rationals.Base

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Archimedean
  using (RationalBound ; ∃rationalBound)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Metric.Radius
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Uniform
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Uniform


-- A whole-line power series is most useful constructively when its local
-- information is retained.  Pointwise summability alone forgets the common
-- tail bound on each bounded interval, which is exactly what continuity,
-- differentiation and later integration need.
--
-- We quantify only over positive rational radii.  Archimedean boundedness
-- makes these radii cofinal among all real points, while avoiding any need
-- to choose a radius as part of the value of the resulting function.

LocallyUniformPowerSeries : RealSequence → Type₀
LocallyUniformPowerSeries coefficients =
  (radius : ℚ₊) →
    PowerSeriesUniformlyCauchyOnRadius
      coefficients (Real.ιℚ (fst radius))


isPropLocallyUniformPowerSeries : ∀ coefficients →
  isProp (LocallyUniformPowerSeries coefficients)
isPropLocallyUniformPowerSeries coefficients =
  isPropΠ λ radius →
    isPropUniformlyCauchySeries
      (ClosedAbsRadius (Real.ιℚ (fst radius)))
      (powerSeriesTermsOnClosedRadius
        coefficients (Real.ιℚ (fst radius)))


-- Mere Archimedean boundedness is enough here because summability is a
-- proposition.  Thus this construction does not extract a radius from a
-- truncation, nor a countable family of convergence moduli.

locallyUniformPowerSeriesSummableAt :
  ∀ coefficients →
  LocallyUniformPowerSeries coefficients →
  ∀ x → PowerSeriesSummableAt coefficients x
locallyUniformPowerSeriesSummableAt coefficients local x =
  PT.rec
    (isPropPowerSeriesSummableAt coefficients x)
    bounded-summable
    (∃rationalBound x)
  where
  bounded-summable : RationalBound x →
    PowerSeriesSummableAt coefficients x
  bounded-summable (radius , absx≤radius) =
    uniformlyCauchySeriesSummableAt
      (ClosedAbsRadius (Real.ιℚ (fst radius)))
      (powerSeriesTermsOnClosedRadius
        coefficients (Real.ιℚ (fst radius)))
      (local radius)
      (x , absx≤radius)


-- The value is canonical because the proof of summability is proposition
-- valued.  In particular, it is definitionally a single whole-line
-- function rather than a compatible family indexed by chosen radii.

opaque
  locallyUniformPowerSeriesValue :
    ∀ coefficients →
    LocallyUniformPowerSeries coefficients →
    Real.ℝ → Real.ℝ
  locallyUniformPowerSeriesValue coefficients local x =
    powerSeriesValue coefficients x
      (locallyUniformPowerSeriesSummableAt coefficients local x)


  locallyUniformPowerSeriesValueHasSum :
    ∀ coefficients local x →
    HasSum
      (powerSeriesTerms coefficients x)
      (locallyUniformPowerSeriesValue coefficients local x)
  locallyUniformPowerSeriesValueHasSum coefficients local x =
    powerSeriesValueHasSum coefficients x
      (locallyUniformPowerSeriesSummableAt coefficients local x)


  -- On every rational closed ball, the whole-line evaluator agrees with the
  -- canonical uniform evaluator.  This is the bridge that lets local analytic
  -- theorems be reused without exposing a radius choice in their statements.

  locallyUniformPowerSeriesValue-agreesOnRadius :
    ∀ coefficients local radius →
    (point : ClosedAbsRadius (Real.ιℚ (fst radius))) →
    locallyUniformPowerSeriesValue coefficients local (fst point)
      ≡
    powerSeriesUniformValueOnClosedRadius
      coefficients (Real.ιℚ (fst radius)) (local radius) point
  locallyUniformPowerSeriesValue-agreesOnRadius
    coefficients local radius point =
    seriesSumIndependent
      (powerSeriesTerms coefficients (fst point))
      (locallyUniformPowerSeriesSummableAt
        coefficients local (fst point))
      (uniformlyCauchySeriesSummableAt
        (ClosedAbsRadius (Real.ιℚ (fst radius)))
        (powerSeriesTermsOnClosedRadius
          coefficients (Real.ιℚ (fst radius)))
        (local radius) point)
