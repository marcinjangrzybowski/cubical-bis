module Cubical.Analysis.Complex.FundamentalTheorem.Matching.EvaluationStep where

-- Keep the Horner estimate independent of recursive completed terms.

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open import Cubical.Data.Rationals.Base using (fromNatℚ)
open import Cubical.Analysis.Real.Algebra.Addition
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ)
open import Cubical.Analysis.Real.Algebra.CommRing using (ℝCommRing)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Complex.Algebra
open import Cubical.Analysis.Complex.Norm
open import Cubical.Analysis.Complex.Norm.Bounds
open import Cubical.Analysis.Complex.Norm.Difference
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.Scale
import Cubical.Analysis.Complex.Algebra.Identities as IdentitiesDefinition

private module R = IdentitiesDefinition.Identities ℝCommRing

opaque
  rationalHornerBound : ∀ a z v A B H →
    normℂ a ≤ℝ ⟦ A ⟧₊ → normℂ z ≤ℝ ⟦ B ⟧₊ → normℂ v ≤ℝ ⟦ H ⟧₊ →
    normℂ (a +ℂ z ·ℂ v) ≤ℝ ⟦ A +₊ (B ·₊ H) ⟧₊
  rationalHornerBound a z v A B H ab zb vb =
    subst {x = ⟦ A ⟧₊ + ⟦ B ⟧₊ · ⟦ H ⟧₊} {y = ⟦ A +₊ (B ·₊ H) ⟧₊}
      (normℂ (a +ℂ z ·ℂ v) ≤ℝ_)
      (cong (⟦ A ⟧₊ +_) (mul-rat (fst B) (fst H)) ∙ rat+rat (fst A) (fst (B ·₊ H)))
      (normℂ-addBound a (z ·ℂ v) ⟦ A ⟧₊ (⟦ B ⟧₊ · ⟦ H ⟧₊) ab
        (normℂ-mulBound z v ⟦ B ⟧₊ ⟦ H ⟧₊ zb vb))

  rationalHornerDifference : ∀ a b r s v w H B L δ →
    normℂ v ≤ℝ ⟦ H ⟧₊ → normℂ s ≤ℝ ⟦ B ⟧₊ →
    normℂ (a -ℂ b) ≤ℝ δ → normℂ (r -ℂ s) ≤ℝ δ → normℂ (v -ℂ w) ≤ℝ ⟦ L ⟧₊ · δ →
    normℂ ((a +ℂ r ·ℂ v) -ℂ (b +ℂ s ·ℂ w)) ≤ℝ ⟦ 1 +₊ (H +₊ (B ·₊ L)) ⟧₊ · δ
  rationalHornerDifference a b r s v w H B L δ vb sb ab rs vw =
    subst (normℂ ((a +ℂ r ·ℂ v) -ℂ (b +ℂ s ·ℂ w)) ≤ℝ_)
      (R.jointHornerBound δ ⟦ H ⟧₊ ⟦ B ⟧₊ ⟦ L ⟧₊ ∙ cong (_· δ) rational-step)
      (normℂ-sumDifference a (r ·ℂ v) b (s ·ℂ w)
        δ (δ · ⟦ H ⟧₊ + ⟦ B ⟧₊ · (⟦ L ⟧₊ · δ)) ab
        (normℂ-productDifference r v s w ⟦ H ⟧₊ ⟦ B ⟧₊ δ (⟦ L ⟧₊ · δ) vb sb rs vw))
    where
    rational-step : 1ℝ + (⟦ H ⟧₊ + ⟦ B ⟧₊ · ⟦ L ⟧₊) ≡ ⟦ 1 +₊ (H +₊ (B ·₊ L)) ⟧₊
    rational-step = cong (1ℝ +_)
      (cong (⟦ H ⟧₊ +_) (mul-rat (fst B) (fst L)) ∙ rat+rat (fst H) (fst (B ·₊ L)))
        ∙ rat+rat 1 (fst (H +₊ (B ·₊ L)))
