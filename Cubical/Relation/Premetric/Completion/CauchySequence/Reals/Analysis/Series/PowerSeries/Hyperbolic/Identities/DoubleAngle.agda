module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.DoubleAngle where

open import Cubical.Foundations.Prelude
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup as Group
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.Constants
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.Shapes.Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.Fundamental

opaque
  sinhℝ-double : ∀ x →
    sinhℝ (x Add.+ x) ≡
      (sinhℝ x Mul.· coshℝ x) Add.+
        (sinhℝ x Mul.· coshℝ x)
  sinhℝ-double x =
      sinhℝ-add x x
    ∙ sinh-double-shape-real
        (sinhℝ x) (coshℝ x)

  coshℝ-double : ∀ x →
    coshℝ (x Add.+ x) ≡
      (coshℝ x Mul.· coshℝ x) Add.+
        (sinhℝ x Mul.· sinhℝ x)
  coshℝ-double x = coshℝ-add x x

  coshℝ-double≡one-add-doubleSinhSquare : ∀ x →
    coshℝ (x Add.+ x) ≡ oneℝ Add.+
      ((sinhℝ x Mul.· sinhℝ x) Add.+
        (sinhℝ x Mul.· sinhℝ x))
  coshℝ-double≡one-add-doubleSinhSquare x =
      coshℝ-double x
    ∙ one-plus-double-sine-shape-real
        (coshℝ x) (sinhℝ x)
    ∙ cong (Add._+ ((sinhℝ x Mul.· sinhℝ x) Add.+
        (sinhℝ x Mul.· sinhℝ x)))
        (coshSquare-sub-sinhSquare≡one x)

  coshℝ-double≡doubleCoshSquare-sub-one : ∀ x →
    coshℝ (x Add.+ x) ≡
      ((coshℝ x Mul.· coshℝ x) Add.+
        (coshℝ x Mul.· coshℝ x)) Group.- oneℝ
  coshℝ-double≡doubleCoshSquare-sub-one x =
      coshℝ-double x
    ∙ double-cosine-minus-one-shape-real
        (coshℝ x) (sinhℝ x)
    ∙ cong (((coshℝ x Mul.· coshℝ x) Add.+
        (coshℝ x Mul.· coshℝ x)) Group.-_)
        (coshSquare-sub-sinhSquare≡one x)
