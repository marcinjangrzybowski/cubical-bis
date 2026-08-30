module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.Fundamental.SinhSquare where

open import Cubical.Foundations.Prelude
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup as Group
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.Constants
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.Shapes.Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.Fundamental.Difference

opaque
  sinhSquare≡coshSquare-sub-one : ∀ x →
    sinhℝ x Mul.· sinhℝ x
      ≡ (coshℝ x Mul.· coshℝ x) Group.- oneℝ
  sinhSquare≡coshSquare-sub-one x =
      remove-difference-real (coshℝ x) (sinhℝ x)
    ∙ cong ((coshℝ x Mul.· coshℝ x) Group.-_)
        (coshSquare-sub-sinhSquare≡one x)
