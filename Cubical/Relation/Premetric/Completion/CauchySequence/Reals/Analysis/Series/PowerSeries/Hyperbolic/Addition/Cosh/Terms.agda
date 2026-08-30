module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Addition.Cosh.Terms where

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Coefficients


coshAddPositive : Real.ℝ → Real.ℝ → Real.ℝ
coshAddPositive x y =
  halfℝ Mul.·
    ((expℝ x Mul.· expℝ y) Add.+ expℝ (Neg.- (x Add.+ y)))

coshAddExpanded : Real.ℝ → Real.ℝ → Real.ℝ
coshAddExpanded x y =
  halfℝ Mul.·
    ((expℝ x Mul.· expℝ y) Add.+
      (expℝ (Neg.- x) Mul.· expℝ (Neg.- y)))

coshAddScaled : Real.ℝ → Real.ℝ → Real.ℝ
coshAddScaled x y =
  ((halfℝ Mul.· halfℝ) Add.+ (halfℝ Mul.· halfℝ)) Mul.·
    ((expℝ x Mul.· expℝ y) Add.+
      (expℝ (Neg.- x) Mul.· expℝ (Neg.- y)))

coshAddShaped : Real.ℝ → Real.ℝ → Real.ℝ
coshAddShaped x y =
  (halfℝ Mul.· (expℝ x Add.+ expℝ (Neg.- x))) Mul.·
    (halfℝ Mul.· (expℝ y Add.+ expℝ (Neg.- y))) Add.+
  (halfℝ Mul.· (expℝ x Add.+ (Neg.- expℝ (Neg.- x)))) Mul.·
    (halfℝ Mul.· (expℝ y Add.+ (Neg.- expℝ (Neg.- y))))

coshAddProduct : Real.ℝ → Real.ℝ → Real.ℝ
coshAddProduct x y =
  (coshℝ x Mul.· coshℝ y) Add.+
    (sinhℝ x Mul.· sinhℝ y)
