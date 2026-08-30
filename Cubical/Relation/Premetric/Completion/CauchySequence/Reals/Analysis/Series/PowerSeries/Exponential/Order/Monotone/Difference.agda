module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Order.Monotone.Difference where

open import Cubical.Foundations.Prelude

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Base
  as Mul
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.GroupLaws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Multiplicative.Congruence.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Structure.AdditiveGroup
  as Group
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Sealed
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Series.PowerSeries.Exponential.Addition.Sealed


differenceℝ : Real.ℝ → Real.ℝ → Real.ℝ
differenceℝ x y = y Group.- x


private
  add-difference : ∀ x y →
    x Add.+ differenceℝ x y ≡ y
  add-difference x y =
      add-comm x (y Group.- x)
    ∙ sub-add-cancel y x


opaque
  expℝ-difference-factorization : ∀ x y →
    expℝ y ≡ expℝ x Mul.· expℝ (differenceℝ x y)
  expℝ-difference-factorization x y =
      expℝ-cong-sealed (sym (add-difference x y))
    ∙ expℝ-add-sealed x (differenceℝ x y)


  sealedExpℝ-difference-factorization : ∀ x y →
    sealedExpℝ y ≡
    sealedExpℝ x Mul.· sealedExpℝ (differenceℝ x y)
  sealedExpℝ-difference-factorization x y =
      sealedExpℝ-agrees y
    ∙ expℝ-difference-factorization x y
    ∙ mul-cong₂-sealed
        (sym (sealedExpℝ-agrees x))
        (sym (sealedExpℝ-agrees (differenceℝ x y)))
