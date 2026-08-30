module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.Subtraction.Cosh.Parity where

open import Cubical.Foundations.Prelude
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.Subtraction.Terms

opaque
  cosh-sub-parity : ∀ x y →
    coshSubAdded (coshℝ x) (sinhℝ x) y ≡
      coshSubParity (coshℝ x) (coshℝ y) (sinhℝ x) (sinhℝ y)
  cosh-sub-parity x y =
    cong₂ Add._+_
      (cong (coshℝ x Mul.·_) (coshℝ-neg y))
      (cong (sinhℝ x Mul.·_) (sinhℝ-neg y))
