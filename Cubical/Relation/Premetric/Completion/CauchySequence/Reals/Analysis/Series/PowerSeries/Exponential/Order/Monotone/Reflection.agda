module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Order.Monotone.Reflection where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sum using (inl ; inr)

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Located
  using (notPositiveGreater→≤ℝ ; ≤ℝ→notPositiveGreater)
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Apartness
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Order.Monotone.NonStrict
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Order.Monotone.Strict


-- Locatedness turns failure of the reverse strict inequality into a
-- non-strict comparison.  Consequently monotonicity reflects non-strict
-- order even though a direct reflection theorem for the positive-gap order
-- would require an additional quantitative estimate.

expℝ-reflects≤ : ∀ {x y} →
  expℝ x ≤ℝ expℝ y → x ≤ℝ y
expℝ-reflects≤ {x} {y} expx≤expy =
  notPositiveGreater→≤ℝ x y λ y<x →
    ≤ℝ→notPositiveGreater
      (expℝ x) (expℝ y) expx≤expy
      (expℝ-strictMono y<x)


expℝ-orderEquiv : ∀ x y →
  (x ≤ℝ y) ≃ (expℝ x ≤ℝ expℝ y)
expℝ-orderEquiv x y =
  propBiimpl→Equiv
    (isProp≤ℝ x y)
    (isProp≤ℝ (expℝ x) (expℝ y))
    expℝ-mono
    expℝ-reflects≤


expℝ-injective : ∀ {x y} →
  expℝ x ≡ expℝ y → x ≡ y
expℝ-injective {x} {y} expx≡expy =
  ≤ℝ-antisym x y
    (expℝ-reflects≤
      (subst (expℝ x ≤ℝ_) expx≡expy
        (≤ℝ-refl (expℝ x))))
    (expℝ-reflects≤
      (subst (_≤ℝ expℝ x) expx≡expy
        (≤ℝ-refl (expℝ x))))


expℝ-preserves-apartness : ∀ x y →
  x ＃ y → expℝ x ＃ expℝ y
expℝ-preserves-apartness x y =
  λ where
    (inl x<y) → inl (expℝ-strictMono x<y)
    (inr y<x) → inr (expℝ-strictMono y<x)
