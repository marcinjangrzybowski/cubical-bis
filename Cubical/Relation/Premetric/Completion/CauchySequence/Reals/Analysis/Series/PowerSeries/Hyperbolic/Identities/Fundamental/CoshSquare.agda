module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.Fundamental.CoshSquare where

open import Cubical.Foundations.Prelude
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.Constants
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.Shapes.Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.Fundamental.Difference

opaque
  coshSquare≡one-add-sinhSquare : ∀ x →
    coshℝ x Mul.· coshℝ x
      ≡ oneℝ Add.+ (sinhℝ x Mul.· sinhℝ x)
  coshSquare≡one-add-sinhSquare x =
      add-removed-square-real (coshℝ x) (sinhℝ x)
    ∙ cong (Add._+ (sinhℝ x Mul.· sinhℝ x))
        (coshSquare-sub-sinhSquare≡one x)
