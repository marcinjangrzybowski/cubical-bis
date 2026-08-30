module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Congruence where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential


-- A sealed congruence boundary prevents clients from unfolding the complete
-- pointwise summability construction merely to transport an input equality.

opaque
  expℝ-cong : ∀ {x y : Real.ℝ} →
    x ≡ y → expℝ x ≡ expℝ y
  expℝ-cong {x} {y} x≡y =
    subst (λ value → expℝ x ≡ expℝ value) x≡y refl
