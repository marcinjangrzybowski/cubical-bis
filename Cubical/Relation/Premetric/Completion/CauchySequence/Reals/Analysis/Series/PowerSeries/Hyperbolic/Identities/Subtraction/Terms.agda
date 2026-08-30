module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.Subtraction.Terms where

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation as Neg
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup as Group
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic

sinhSubAdded : Real.ℝ → Real.ℝ → Real.ℝ → Real.ℝ
sinhSubAdded sinhX coshX y =
  (sinhX Mul.· coshℝ (Neg.- y)) Add.+
    (coshX Mul.· sinhℝ (Neg.- y))

sinhSubParity : Real.ℝ → Real.ℝ → Real.ℝ → Real.ℝ → Real.ℝ
sinhSubParity sinhX sinhY coshX coshY =
  (sinhX Mul.· coshY) Add.+
    (coshX Mul.· (Neg.- sinhY))

sinhSubResult : Real.ℝ → Real.ℝ → Real.ℝ → Real.ℝ → Real.ℝ
sinhSubResult sinhX sinhY coshX coshY =
  (sinhX Mul.· coshY) Group.- (coshX Mul.· sinhY)

coshSubAdded : Real.ℝ → Real.ℝ → Real.ℝ → Real.ℝ
coshSubAdded coshX sinhX y =
  (coshX Mul.· coshℝ (Neg.- y)) Add.+
    (sinhX Mul.· sinhℝ (Neg.- y))

coshSubParity : Real.ℝ → Real.ℝ → Real.ℝ → Real.ℝ → Real.ℝ
coshSubParity coshX coshY sinhX sinhY =
  (coshX Mul.· coshY) Add.+
    (sinhX Mul.· (Neg.- sinhY))

coshSubResult : Real.ℝ → Real.ℝ → Real.ℝ → Real.ℝ → Real.ℝ
coshSubResult coshX coshY sinhX sinhY =
  (coshX Mul.· coshY) Group.- (sinhX Mul.· sinhY)
