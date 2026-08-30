module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Interior where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Rationals.Base
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.AbsoluteValue
  as Abs
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
  using (_≤ℝ_)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base
  using (_<ℝ_ ; <ℝ-weaken)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Interior
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Majorant
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Uniform
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Difference.Uniform
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Difference.Derivative


-- Closed-radius termwise differentiation yields an ordinary derivative at
-- every strict interior point once an ambient function agrees with the
-- canonical uniform sum.  Requiring the extension explicitly avoids
-- pretending that convergence has defined the series outside this radius.

powerSeriesUniformValueHasFormalDerivativeAtInteriorWithExtension :
  ∀ coefficients radius →
  (uniform :
    PowerSeriesUniformlyCauchyOnRadius coefficients radius) →
  (derivative-uniform :
    PowerSeriesUniformlyCauchyOnRadius
      (formalDerivative coefficients) radius) →
  (factor-uniform :
    PowerSeriesDifferenceFactorUniformlyCauchyOnRadius
      coefficients radius) →
  (function : Real.ℝ → Real.ℝ) →
  (∀ point →
    function (fst point)
      ≡
    powerSeriesUniformValueOnClosedRadius
      coefficients radius uniform point) →
  ∀ x →
  (interior : Abs.absℝ x <ℝ radius) →
  IsDerivativeAt
    function
    (powerSeriesUniformValueOnClosedRadius
      (formalDerivative coefficients)
      radius derivative-uniform
      (x , <ℝ-weaken (Abs.absℝ x) radius interior))
    x
powerSeriesUniformValueHasFormalDerivativeAtInteriorWithExtension
  coefficients radius uniform derivative-uniform factor-uniform
  function agrees x interior =
    closedAbsRadiusDerivativeAtInteriorWithExtension
      radius
      (powerSeriesUniformValueOnClosedRadius
        coefficients radius uniform)
      (powerSeriesUniformValueOnClosedRadius
        (formalDerivative coefficients) radius derivative-uniform)
      function
      (powerSeriesUniformValueHasFormalDerivativeOnClosedRadius
        coefficients radius uniform derivative-uniform factor-uniform)
      agrees x interior


-- Rather than bake a large, derived uniformity proof into the type of the
-- derivative value, the majorant interface returns that proof together with
-- the derivative.  This is stronger operationally: callers can reuse the
-- same witness for continuity and further termwise constructions, while its
-- proposition-valued tails still require no choice principle.

powerSeriesUniformValueHasFormalDerivativeAtInteriorByMajorantWithinExtension :
  ∀ coefficients majorant inner-radius outer-radius →
  (majorized : CoefficientMajorizedBy coefficients majorant) →
  (inner-nonnegative : Real.ιℚ 0 ≤ℝ inner-radius) →
  (inner≤outer : inner-radius ≤ℝ outer-radius) →
  (uniform :
    PowerSeriesUniformlyCauchyOnRadius coefficients inner-radius) →
  (outer-derivative-majorant-cauchy :
    IsCauchySeries
      (powerSeriesTerms
        (formalDerivativeMajorant majorant) outer-radius)) →
  (function : Real.ℝ → Real.ℝ) →
  (∀ point →
    function (fst point)
      ≡
    powerSeriesUniformValueOnClosedRadius
      coefficients inner-radius uniform point) →
  ∀ x →
  (interior : Abs.absℝ x <ℝ inner-radius) →
  Σ[ derivative-uniform ∈
      PowerSeriesUniformlyCauchyOnRadius
        (formalDerivative coefficients) inner-radius ]
    IsDerivativeAt
      function
      (powerSeriesUniformValueOnClosedRadius
        (formalDerivative coefficients)
        inner-radius derivative-uniform
        (x , <ℝ-weaken
          (Abs.absℝ x) inner-radius interior))
      x
powerSeriesUniformValueHasFormalDerivativeAtInteriorByMajorantWithinExtension
  coefficients majorant inner-radius outer-radius
  majorized inner-nonnegative inner≤outer uniform
  outer-derivative-majorant-cauchy function agrees x interior =
    derivative-uniform
    , powerSeriesUniformValueHasFormalDerivativeAtInteriorWithExtension
        coefficients inner-radius uniform
        derivative-uniform factor-uniform
        function agrees x interior
  where
  derivative-uniform :
    PowerSeriesUniformlyCauchyOnRadius
      (formalDerivative coefficients) inner-radius
  derivative-uniform =
    formalDerivativePowerSeriesUniformlyCauchyWithin
      coefficients majorant inner-radius outer-radius
      majorized inner-nonnegative inner≤outer
      outer-derivative-majorant-cauchy

  factor-uniform :
    PowerSeriesDifferenceFactorUniformlyCauchyOnRadius
      coefficients inner-radius
  factor-uniform =
    powerSeriesDifferenceFactorUniformlyCauchyByDerivativeMajorantWithin
      coefficients majorant inner-radius outer-radius
      majorized inner-nonnegative inner≤outer
      outer-derivative-majorant-cauchy


powerSeriesUniformValueHasFormalDerivativeAtInteriorByMajorantWithinStrictExtension :
  ∀ coefficients majorant inner-radius outer-radius →
  (majorized : CoefficientMajorizedBy coefficients majorant) →
  (inner-nonnegative : Real.ιℚ 0 ≤ℝ inner-radius) →
  (inner<outer : inner-radius <ℝ outer-radius) →
  (uniform :
    PowerSeriesUniformlyCauchyOnRadius coefficients inner-radius) →
  (outer-derivative-majorant-cauchy :
    IsCauchySeries
      (powerSeriesTerms
        (formalDerivativeMajorant majorant) outer-radius)) →
  (function : Real.ℝ → Real.ℝ) →
  (∀ point →
    function (fst point)
      ≡
    powerSeriesUniformValueOnClosedRadius
      coefficients inner-radius uniform point) →
  ∀ x →
  (interior : Abs.absℝ x <ℝ inner-radius) →
  Σ[ derivative-uniform ∈
      PowerSeriesUniformlyCauchyOnRadius
        (formalDerivative coefficients) inner-radius ]
    IsDerivativeAt
      function
      (powerSeriesUniformValueOnClosedRadius
        (formalDerivative coefficients)
        inner-radius derivative-uniform
        (x , <ℝ-weaken
          (Abs.absℝ x) inner-radius interior))
      x
powerSeriesUniformValueHasFormalDerivativeAtInteriorByMajorantWithinStrictExtension
  coefficients majorant inner-radius outer-radius
  majorized inner-nonnegative inner<outer uniform
  outer-derivative-majorant-cauchy function agrees x interior =
    powerSeriesUniformValueHasFormalDerivativeAtInteriorByMajorantWithinExtension
      coefficients majorant inner-radius outer-radius
      majorized inner-nonnegative
      (<ℝ-weaken inner-radius outer-radius inner<outer)
      uniform outer-derivative-majorant-cauchy
      function agrees x interior
