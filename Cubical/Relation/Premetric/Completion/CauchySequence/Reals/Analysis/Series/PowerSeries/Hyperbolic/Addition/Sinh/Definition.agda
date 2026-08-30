module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Addition.Sinh.Definition where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Congruence.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Congruence.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Base.Definitions.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Addition.Sinh.Terms


opaque
  sinhℝ-add-definition : ∀ x y →
    sinhAddShaped x y ≡ sinhAddProduct x y
  sinhℝ-add-definition x y =
    add-cong₂-sealed
      (mul-cong₂-sealed
        (sym (sinhℝ-definition-sealed x))
        (sym (coshℝ-definition-sealed y)))
      (mul-cong₂-sealed
        (sym (coshℝ-definition-sealed x))
        (sym (sinhℝ-definition-sealed y)))
