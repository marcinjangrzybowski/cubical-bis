module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Base.Definitions where

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Coefficients


sinhℝ : Real.ℝ → Real.ℝ
sinhℝ x =
  halfℝ Mul.· (expℝ x Group.- expℝ (Neg.- x))


coshℝ : Real.ℝ → Real.ℝ
coshℝ x =
  halfℝ Mul.· (expℝ x Add.+ expℝ (Neg.- x))
