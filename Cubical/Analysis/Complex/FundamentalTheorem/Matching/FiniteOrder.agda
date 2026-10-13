module Cubical.Analysis.Complex.FundamentalTheorem.Matching.FiniteOrder where

-- Finite located search with an overlap margin. Abstracting the values
-- keeps completed complex expressions out of the recursive case splits.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.FinData using (Fin; zero; suc)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Analysis.Real.Base using (ℝ)
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base using (_<ℝ_)
open import Cubical.Analysis.Real.Order.Strict.Properties using (<ℝ-weaken)
open import Cubical.Analysis.Real.Order.Strict.Located using (dichotomyℝ)
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open import Cubical.Analysis.Real.Algebra.Multiplication
open import Cubical.Analysis.Real.Algebra.AdditionLaws using (0ℝ)
open import Cubical.Analysis.Real.Algebra.Multiplication.Laws using (1ℝ)
open import Cubical.Analysis.Real.Order.Multiplication
open import Cubical.Analysis.Complex.FundamentalTheorem.Matching.Scale
open import Cubical.Algebra.CommRing using (CommRing→Ring)
import Cubical.Algebra.Ring.BigOps as BigOps
open import Cubical.Analysis.Real.Algebra.CommRing using (ℝCommRing)

FiniteOrderAlternative : ∀ n → (Fin n → ℝ) → ℝ → ℝ → Type₀
FiniteOrderAlternative n values lo hi = PT.∥
  (Σ[ i ∈ Fin n ] (values i <ℝ hi)) ⊎ (∀ i → lo ≤ℝ values i) ∥₁

finiteOrderAlternative : ∀ n values lo hi → lo <ℝ hi → FiniteOrderAlternative n values lo hi
finiteOrderAlternative zero values lo hi gap = PT.∣ inr (λ ()) ∣₁
finiteOrderAlternative (suc n) values lo hi gap = PT.rec PT.isPropPropTrunc cases
  (dichotomyℝ lo (values zero) hi gap)
  where
  cases : (values zero <ℝ hi) ⊎ (lo <ℝ values zero) → FiniteOrderAlternative (suc n) values lo hi
  cases (inl near) = PT.∣ inl (zero , near) ∣₁
  cases (inr far) = PT.map combine (finiteOrderAlternative n (λ i → values (suc i)) lo hi gap)
    where
    combine : (Σ[ i ∈ Fin n ] (values (suc i) <ℝ hi)) ⊎ (∀ i → lo ≤ℝ values (suc i)) →
      (Σ[ i ∈ Fin (suc n) ] (values i <ℝ hi)) ⊎ (∀ i → lo ≤ℝ values i)
    combine (inl (i , near)) = inl (suc i , near)
    combine (inr all-far) = inr λ { zero → <ℝ-weaken lo (values zero) far
                                ; (suc i) → all-far i }

finiteRealProduct : ∀ n → (Fin n → ℝ) → ℝ
finiteRealProduct n = BigOps.Product.∏ (CommRing→Ring ℝCommRing) {n = n}

finitePositivePower : ℕ → ℚ₊ → ℚ₊
finitePositivePower zero a = 1
finitePositivePower (suc n) a = a ·₊ finitePositivePower n a

opaque
  finiteProduct-lower : ∀ n values a → (∀ i → ⟦ a ⟧₊ ≤ℝ values i) →
    ⟦ finitePositivePower n a ⟧₊ ≤ℝ finiteRealProduct n values
  finiteProduct-lower zero values a below = ≤ℝ-refl 1ℝ
  finiteProduct-lower (suc n) values a below =
    subst (_≤ℝ finiteRealProduct (suc n) values) (mul-rat (fst a) (fst (finitePositivePower n a)))
      (mulPres≤ ⟦ a ⟧₊ (values zero) ⟦ finitePositivePower n a ⟧₊
        (finiteRealProduct n (λ i → values (suc i)))
        (≤ℝ-trans 0ℝ ⟦ a ⟧₊ (values zero) (radius-nonnegative a) (below zero))
        (radius-nonnegative (finitePositivePower n a)) (below zero)
        (finiteProduct-lower n (λ i → values (suc i)) a (λ i → below (suc i))))
