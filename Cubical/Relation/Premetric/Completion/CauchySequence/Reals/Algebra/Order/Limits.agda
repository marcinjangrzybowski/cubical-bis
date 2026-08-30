module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Limits where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Nat.Base as ℕ using (ℕ ; zero)
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base


constantIsCauchySequence : ∀ x → Real.Base.IsCauchySequence (λ _ → x)
constantIsCauchySequence x ε =
  ∣ zero , (λ _ _ _ _ → Real.Base.isRefl≈ᶜ x ε) ∣₁

private
  lim-cong : ∀ {x y : ℕ → Real.ℝ}
    (gx : Real.Base.IsCauchySequence x) (gy : Real.Base.IsCauchySequence y) →
    x ≡ y → Real.Base.lim x gx ≡ Real.Base.lim y gy
  lim-cong {x} {y} gx gy p =
    cong (λ z → Real.Base.lim (fst z) (snd z))
      (Σ≡Prop Real.Base.isPropIsCauchySequence p)

  eventuallyConstant-isLimitSeq : ∀ z N b →
    (∀ n → N ℕ.≤ n → z n ≡ b) →
    Real.Premetric.CompletionTheory.isLimitSeq z b
  eventuallyConstant-isLimitSeq z N b eventually ε =
    ∣ N , (λ n N≤n →
      subst (Real.Base._≈ᶜ[ ε ] b)
        (sym (eventually n N≤n))
        (Real.Base.isRefl≈ᶜ b ε)) ∣₁


lim-constant : ∀ x gx → Real.Base.lim (λ _ → x) gx ≡ x
lim-constant x gx =
  cong fst
    (Real.Premetric.CompletionTheory.isPropLimitSeq (λ _ → x)
      (Real.Base.lim (λ _ → x) gx , Real.Premetric.lim-isLimitSeq _ gx)
      (x , eventuallyConstant-isLimitSeq (λ _ → x) zero x
        (λ _ _ → refl)))

lim-eventuallyConstant : ∀ z gz N b →
  (∀ n → N ℕ.≤ n → z n ≡ b) → Real.Base.lim z gz ≡ b
lim-eventuallyConstant z gz N b eventually =
  cong fst
    (Real.Premetric.CompletionTheory.isPropLimitSeq z
      (Real.Base.lim z gz , Real.Premetric.lim-isLimitSeq z gz)
      (b , eventuallyConstant-isLimitSeq z N b eventually))


lim-preserves≤ : ∀ x gx y gy →
  (∀ n → x n ≤ℝ y n) →
  Real.Base.lim x gx ≤ℝ Real.Base.lim y gy
lim-preserves≤ x gx y gy pointwise =
    max-lim-lim x gx y gy
  ∙ lim-cong _ gy (funExt pointwise)

lim-upper-bound-eventually : ∀ x gx N b →
  (∀ n → N ℕ.≤ n → x n ≤ℝ b) →
  Real.Base.lim x gx ≤ℝ b
lim-upper-bound-eventually x gx N b bounded =
    max-lim-left x gx b
  ∙ lim-eventuallyConstant (λ n → x n ⊔ℝ b) _ N b bounded
