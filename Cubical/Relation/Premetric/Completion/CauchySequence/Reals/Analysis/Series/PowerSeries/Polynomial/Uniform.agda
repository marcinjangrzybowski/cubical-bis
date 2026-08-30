module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Polynomial.Uniform where

open import Cubical.Foundations.Prelude

open import Cubical.Data.List using (List ; length)
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Premetric.Base

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Polynomial
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Derivative.Polynomial
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Metric.Radius
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Uniform
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Polynomial
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Uniform


-- Finite support gives a single cutoff valid simultaneously for every point
-- and every radius.  In the native interface that cutoff remains under the
-- truncation at the requested precision; we do not manufacture a global
-- modulus merely because this special family happens to have one.

polynomialPowerSeriesUniformlyCauchyOnRadius :
  ∀ coefficients radius →
  PowerSeriesUniformlyCauchyOnRadius
    (polynomialCoefficientSequence coefficients) radius
polynomialPowerSeriesUniformlyCauchyOnRadius
  coefficients radius ε =
  ∣ length coefficients
  , (λ point m n length≤m length≤n →
    let finite-sum : Real.ℝ
        finite-sum =
          partialSum
            (powerSeriesTerms
              (polynomialCoefficientSequence coefficients)
              (fst point))
            (length coefficients)
    in
      subst2 (Real.Base._≈ᶜ[ ε ]_)
        (sym (polynomialPowerSeriesPartialSumStableAbove
          coefficients (fst point) m length≤m))
        (sym (polynomialPowerSeriesPartialSumStableAbove
          coefficients (fst point) n length≤n))
        (Real.Base.isRefl≈ᶜ finite-sum ε))
  ∣₁


polynomialPowerSeriesFunctionOnClosedRadius :
  List Real.ℝ → ∀ radius → ClosedAbsRadius radius → Real.ℝ
polynomialPowerSeriesFunctionOnClosedRadius coefficients radius =
  powerSeriesUniformValueOnClosedRadius
    (polynomialCoefficientSequence coefficients) radius
    (polynomialPowerSeriesUniformlyCauchyOnRadius coefficients radius)


opaque
  polynomialPowerSeriesFunctionOnClosedRadius-value :
    ∀ coefficients radius point →
    polynomialPowerSeriesFunctionOnClosedRadius coefficients radius point ≡
    evaluatePolynomial coefficients (fst point)
  polynomialPowerSeriesFunctionOnClosedRadius-value
    coefficients radius point =
    polynomialPowerSeriesValue coefficients (fst point)
      (uniformlyCauchySeriesSummableAt
        (ClosedAbsRadius radius)
        (powerSeriesTermsOnClosedRadius
          (polynomialCoefficientSequence coefficients) radius)
        (polynomialPowerSeriesUniformlyCauchyOnRadius coefficients radius)
        point)

