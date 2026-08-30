module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Congruence.Sealed where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Hyperbolic.Base


opaque
  sinhℝ-cong-sealed : ∀ {x y : Real.ℝ} →
    x ≡ y → sinhℝ x ≡ sinhℝ y
  sinhℝ-cong-sealed = cong sinhℝ

  coshℝ-cong-sealed : ∀ {x y : Real.ℝ} →
    x ≡ y → coshℝ x ≡ coshℝ y
  coshℝ-cong-sealed = cong coshℝ
