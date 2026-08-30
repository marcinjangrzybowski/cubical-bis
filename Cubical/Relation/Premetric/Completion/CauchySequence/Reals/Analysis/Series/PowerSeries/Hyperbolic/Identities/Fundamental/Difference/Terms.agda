module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.Fundamental.Difference.Terms where

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation as Neg
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup as Group
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic

fundamentalTranslated : Real.ℝ → Real.ℝ
fundamentalTranslated x =
  (coshℝ x Mul.· coshℝ (Neg.- x)) Add.+
    (sinhℝ x Mul.· sinhℝ (Neg.- x))

fundamentalParity : Real.ℝ → Real.ℝ
fundamentalParity x =
  (coshℝ x Mul.· coshℝ x) Add.+
    (sinhℝ x Mul.· (Neg.- sinhℝ x))

fundamentalDifference : Real.ℝ → Real.ℝ
fundamentalDifference x =
  (coshℝ x Mul.· coshℝ x) Group.-
    (sinhℝ x Mul.· sinhℝ x)
