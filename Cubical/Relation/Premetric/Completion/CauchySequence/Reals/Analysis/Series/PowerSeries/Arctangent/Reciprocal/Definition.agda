module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Arctangent.Reciprocal.Definition where

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Arctangent.Prelude
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Arctangent.Reciprocal.Ratio
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals as Real
open import Cubical.Data.Rationals.Order as ℚ

arctangentReciprocalOnClosedRadius :
  (q : ℚ₊) → (q<1 : fst q ℚ.< 1) →
  ClosedAbsRadius (Real.ιℚ (fst q)) → Real.ℝ
arctangentReciprocalOnClosedRadius q q<1 point =
  geometricReciprocal
    (arctangentRatio (fst point))
    (arctangentRatio<one q q<1 point)
