module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Addition.Sinh.Terms where

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
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Coefficients


sinhAddPositive : Real.ℝ → Real.ℝ → Real.ℝ
sinhAddPositive x y =
  halfℝ Mul.·
    ((expℝ x Mul.· expℝ y) Group.- expℝ (Neg.- (x Add.+ y)))

sinhAddExpanded : Real.ℝ → Real.ℝ → Real.ℝ
sinhAddExpanded x y =
  halfℝ Mul.·
    ((expℝ x Mul.· expℝ y) Add.+
      (Neg.- (expℝ (Neg.- x) Mul.· expℝ (Neg.- y))))

sinhAddScaled : Real.ℝ → Real.ℝ → Real.ℝ
sinhAddScaled x y =
  ((halfℝ Mul.· halfℝ) Add.+ (halfℝ Mul.· halfℝ)) Mul.·
    ((expℝ x Mul.· expℝ y) Add.+
      (Neg.- (expℝ (Neg.- x) Mul.· expℝ (Neg.- y))))

sinhAddShaped : Real.ℝ → Real.ℝ → Real.ℝ
sinhAddShaped x y =
  (halfℝ Mul.· (expℝ x Add.+ (Neg.- expℝ (Neg.- x)))) Mul.·
    (halfℝ Mul.· (expℝ y Add.+ expℝ (Neg.- y))) Add.+
  (halfℝ Mul.· (expℝ x Add.+ expℝ (Neg.- x))) Mul.·
    (halfℝ Mul.· (expℝ y Add.+ (Neg.- expℝ (Neg.- y))))

sinhAddProduct : Real.ℝ → Real.ℝ → Real.ℝ
sinhAddProduct x y =
  (sinhℝ x Mul.· coshℝ y) Add.+
    (coshℝ x Mul.· sinhℝ y)
