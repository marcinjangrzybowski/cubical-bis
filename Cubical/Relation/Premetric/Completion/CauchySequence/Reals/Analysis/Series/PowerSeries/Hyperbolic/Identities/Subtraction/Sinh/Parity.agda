module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.Subtraction.Sinh.Parity where

open import Cubical.Foundations.Prelude
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.Subtraction.Terms

opaque
  sinh-sub-parity : ∀ x y →
    sinhSubAdded (sinhℝ x) (coshℝ x) y ≡
      sinhSubParity (sinhℝ x) (sinhℝ y) (coshℝ x) (coshℝ y)
  sinh-sub-parity x y =
    cong₂ Add._+_
      (cong (sinhℝ x Mul.·_) (coshℝ-neg y))
      (cong (coshℝ x Mul.·_) (sinhℝ-neg y))
