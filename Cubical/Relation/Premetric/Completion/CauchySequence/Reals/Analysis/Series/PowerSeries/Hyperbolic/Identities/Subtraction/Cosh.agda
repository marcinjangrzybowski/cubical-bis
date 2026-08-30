module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.Subtraction.Cosh where

open import Cubical.Foundations.Prelude
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup as Group
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.Subtraction.Cosh.Domain
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.Subtraction.Cosh.Addition
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.Subtraction.Cosh.Parity
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.Subtraction.Cosh.Shape

opaque
  coshℝ-sub : ∀ x y →
    coshℝ (x Group.- y) ≡
      (coshℝ x Mul.· coshℝ y) Group.-
        (sinhℝ x Mul.· sinhℝ y)
  coshℝ-sub x y =
      cosh-sub-domain x y
    ∙ cosh-sub-addition x y
    ∙ cosh-sub-parity x y
    ∙ cosh-sub-shape x y
