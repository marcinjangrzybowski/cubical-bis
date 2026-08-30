module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Sealed where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential


-- The public exponential remains `expℝ`.  This opaque alias is only a
-- normalization boundary for congruence and transport: its agreement path
-- makes crossing the boundary explicit without duplicating any evaluator.

opaque
  sealedExpℝ : Real.ℝ → Real.ℝ
  sealedExpℝ = expℝ

  sealedExpℝ-agrees : ∀ x → sealedExpℝ x ≡ expℝ x
  sealedExpℝ-agrees x = refl


opaque
  sealedExpℝ-cong : ∀ {x y : Real.ℝ} →
    x ≡ y → sealedExpℝ x ≡ sealedExpℝ y
  sealedExpℝ-cong {x} {y} x≡y =
    subst
      (λ value → sealedExpℝ x ≡ sealedExpℝ value)
      x≡y refl


opaque
  expℝ-cong-sealed : ∀ {x y : Real.ℝ} →
    x ≡ y → expℝ x ≡ expℝ y
  expℝ-cong-sealed {x} {y} x≡y =
      sym (sealedExpℝ-agrees x)
    ∙ sealedExpℝ-cong x≡y
    ∙ sealedExpℝ-agrees y
