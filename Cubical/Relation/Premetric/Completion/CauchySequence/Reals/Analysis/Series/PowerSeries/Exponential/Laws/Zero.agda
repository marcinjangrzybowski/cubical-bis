module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Laws.Zero where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Rationals.Base

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.AtZero
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential


-- Evaluation at zero is a construction-level power-series fact.  Using the
-- generic theorem avoids proving it indirectly by cancellation through a
-- proof-indexed positive reciprocal.

opaque
  expℝ-zero : expℝ zeroℝ ≡ Real.ιℚ 1
  expℝ-zero =
      powerSeriesValueAtZero
        exponentialCoefficients
        (exponentialPowerSeriesIsSummable zeroℝ)
    ∙ exponentialCoefficient-zero
