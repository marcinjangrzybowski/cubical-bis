module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.ProductToSum where

open import Cubical.Foundations.Prelude
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup as Group
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.Shapes.Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.Subtraction

opaque
  coshℝ-add-plus-coshℝ-sub : ∀ x y →
    coshℝ (x Add.+ y) Add.+ coshℝ (x Group.- y) ≡
      (coshℝ x Mul.· coshℝ y) Add.+
        (coshℝ x Mul.· coshℝ y)
  coshℝ-add-plus-coshℝ-sub x y =
      cong₂ Add._+_ (coshℝ-add x y) (coshℝ-sub x y)
    ∙ cosh-sum-shape-real
        (coshℝ x) (coshℝ y) (sinhℝ x) (sinhℝ y)

  coshℝ-add-minus-coshℝ-sub : ∀ x y →
    coshℝ (x Add.+ y) Group.- coshℝ (x Group.- y) ≡
      (sinhℝ x Mul.· sinhℝ y) Add.+
        (sinhℝ x Mul.· sinhℝ y)
  coshℝ-add-minus-coshℝ-sub x y =
      cong₂ Group._-_ (coshℝ-add x y) (coshℝ-sub x y)
    ∙ cosh-difference-shape-real
        (coshℝ x) (coshℝ y) (sinhℝ x) (sinhℝ y)

  sinhℝ-add-plus-sinhℝ-sub : ∀ x y →
    sinhℝ (x Add.+ y) Add.+ sinhℝ (x Group.- y) ≡
      (sinhℝ x Mul.· coshℝ y) Add.+
        (sinhℝ x Mul.· coshℝ y)
  sinhℝ-add-plus-sinhℝ-sub x y =
      cong₂ Add._+_ (sinhℝ-add x y) (sinhℝ-sub x y)
    ∙ sinh-sum-shape-real
        (sinhℝ x) (sinhℝ y) (coshℝ x) (coshℝ y)

  sinhℝ-add-minus-sinhℝ-sub : ∀ x y →
    sinhℝ (x Add.+ y) Group.- sinhℝ (x Group.- y) ≡
      (coshℝ x Mul.· sinhℝ y) Add.+
        (coshℝ x Mul.· sinhℝ y)
  sinhℝ-add-minus-sinhℝ-sub x y =
      cong₂ Group._-_ (sinhℝ-add x y) (sinhℝ-sub x y)
    ∙ sinh-difference-shape-real
        (sinhℝ x) (sinhℝ y) (coshℝ x) (coshℝ y)
