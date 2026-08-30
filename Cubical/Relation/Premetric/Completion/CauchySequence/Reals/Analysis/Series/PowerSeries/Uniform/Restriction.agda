module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Uniform.Restriction where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Metric.Radius
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Uniform
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Uniform.Reindex
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Uniform


-- Closed absolute balls form a contravariant system for uniform power-series
-- convergence.  This theorem needs no coefficient majorant and therefore
-- applies equally to convergence obtained by comparison, algebraic
-- operations, or a concrete Cauchy witness.

restrictClosedAbsRadius : ∀ {inner-radius outer-radius} →
  inner-radius ≤ℝ outer-radius →
  ClosedAbsRadius inner-radius →
  ClosedAbsRadius outer-radius
restrictClosedAbsRadius {inner-radius} {outer-radius}
  inner≤outer (x , absx≤inner) =
  x , ≤ℝ-trans
    (Abs.absℝ x) inner-radius outer-radius
    absx≤inner inner≤outer


powerSeriesUniformlyCauchyRestrictRadius :
  ∀ coefficients inner-radius outer-radius →
  inner-radius ≤ℝ outer-radius →
  PowerSeriesUniformlyCauchyOnRadius coefficients outer-radius →
  PowerSeriesUniformlyCauchyOnRadius coefficients inner-radius
powerSeriesUniformlyCauchyRestrictRadius
  coefficients inner-radius outer-radius inner≤outer uniform =
  uniformlyCauchySeriesPrecompose
    (ClosedAbsRadius inner-radius)
    (ClosedAbsRadius outer-radius)
    (powerSeriesTermsOnClosedRadius coefficients outer-radius)
    uniform
    (restrictClosedAbsRadius inner≤outer)


powerSeriesUniformlyAbsolutelyCauchyRestrictRadius :
  ∀ coefficients inner-radius outer-radius →
  inner-radius ≤ℝ outer-radius →
  PowerSeriesUniformlyAbsolutelyCauchyOnRadius
    coefficients outer-radius →
  PowerSeriesUniformlyAbsolutelyCauchyOnRadius
    coefficients inner-radius
powerSeriesUniformlyAbsolutelyCauchyRestrictRadius
  coefficients inner-radius outer-radius inner≤outer uniform =
  uniformlyAbsolutelyCauchySeriesPrecompose
    (ClosedAbsRadius inner-radius)
    (ClosedAbsRadius outer-radius)
    (powerSeriesTermsOnClosedRadius coefficients outer-radius)
    uniform
    (restrictClosedAbsRadius inner≤outer)


powerSeriesUniformValueRestrictRadius :
  ∀ coefficients inner-radius outer-radius
    (inner≤outer : inner-radius ≤ℝ outer-radius)
    (uniform :
      PowerSeriesUniformlyCauchyOnRadius coefficients outer-radius)
    (point : ClosedAbsRadius inner-radius) →
  powerSeriesUniformValueOnClosedRadius coefficients inner-radius
      (powerSeriesUniformlyCauchyRestrictRadius
        coefficients inner-radius outer-radius inner≤outer uniform)
      point
    ≡
  powerSeriesUniformValueOnClosedRadius coefficients outer-radius uniform
    (restrictClosedAbsRadius inner≤outer point)
powerSeriesUniformValueRestrictRadius
  coefficients inner-radius outer-radius inner≤outer uniform point =
  uniformSeriesValuePrecompose
    (ClosedAbsRadius inner-radius)
    (ClosedAbsRadius outer-radius)
    (powerSeriesTermsOnClosedRadius coefficients outer-radius)
    uniform
    (restrictClosedAbsRadius inner≤outer)
    point
