module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.Fundamental.Difference.Parity where

open import Cubical.Foundations.Prelude
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation as Neg
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Identities.Fundamental.Difference.Terms

opaque
  fundamentalTranslated≡parity : ∀ x →
    fundamentalTranslated x ≡ fundamentalParity x
  fundamentalTranslated≡parity x =
    cong₂ Add._+_
      (cong (coshℝ x Mul.·_) (coshℝ-neg x))
      (cong (sinhℝ x Mul.·_) (sinhℝ-neg x))
