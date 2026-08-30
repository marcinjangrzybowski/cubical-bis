module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Laws where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat.Base using (ℕ)
open import Cubical.Data.Rationals.Base as ℚ
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Sigma

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base


private
  lim-cong : ∀ {x y : ℕ → Real.ℝ}
    (gx : Real.Base.IsCauchySequence x) (gy : Real.Base.IsCauchySequence y) →
    x ≡ y → Real.Base.lim x gx ≡ Real.Base.lim y gy
  lim-cong {x} {y} gx gy p =
    cong (λ z → Real.Base.lim (fst z) (snd z))
      (Σ≡Prop Real.Base.isPropIsCauchySequence p)


-- Associativity is inherited from rational max by three constructor
-- inductions.  Limit arguments occurring on the right are first moved to
-- the left by commutativity, so every branch can use `max-lim-left` with its
-- already determined tail witness.  No comparison with another real-number
-- construction is involved.

private
  max-assoc-inner : ∀ p q → Real.Base.ElimCompletion-Prop
    (λ z →
      Real.ιℚ p ⊔ℝ (Real.ιℚ q ⊔ℝ z) ≡
      (Real.ιℚ p ⊔ℝ Real.ιℚ q) ⊔ℝ z)
  max-assoc-inner p q .Real.Base.ElimCompletion-Prop.ιA r =
      cong (Real.ιℚ p ⊔ℝ_) (max-ι q r)
    ∙ max-ι p (ℚ.max q r)
    ∙ cong Real.ιℚ (ℚ.maxAssoc p q r)
    ∙ sym (max-ι (ℚ.max p q) r)
    ∙ cong (_⊔ℝ Real.ιℚ r) (sym (max-ι p q))
  max-assoc-inner p q .Real.Base.ElimCompletion-Prop.limA z gz IH =
      max-comm (Real.ιℚ p) (Real.ιℚ q ⊔ℝ Real.Base.lim z gz)
    ∙ cong (_⊔ℝ Real.ιℚ p)
        (max-comm (Real.ιℚ q) (Real.Base.lim z gz))
    ∙ cong (_⊔ℝ Real.ιℚ p) (max-lim-left z gz (Real.ιℚ q))
    ∙ max-lim-left (λ n → z n ⊔ℝ Real.ιℚ q) _ (Real.ιℚ p)
    ∙ lim-cong _ _ (funExt λ n →
        max-comm (z n ⊔ℝ Real.ιℚ q) (Real.ιℚ p)
      ∙ cong (Real.ιℚ p ⊔ℝ_) (max-comm (z n) (Real.ιℚ q))
      ∙ IH n
      ∙ max-comm (Real.ιℚ p ⊔ℝ Real.ιℚ q) (z n))
    ∙ sym (max-lim-left z gz (Real.ιℚ p ⊔ℝ Real.ιℚ q))
    ∙ sym (max-comm
        (Real.ιℚ p ⊔ℝ Real.ιℚ q) (Real.Base.lim z gz))
  max-assoc-inner p q .Real.Base.ElimCompletion-Prop.isPropA z =
    Real.Base.isSetCompletion _ _

  max-assoc-middle : ∀ p → Real.Base.ElimCompletion-Prop
    (λ y → ∀ z →
      Real.ιℚ p ⊔ℝ (y ⊔ℝ z) ≡
      (Real.ιℚ p ⊔ℝ y) ⊔ℝ z)
  max-assoc-middle p .Real.Base.ElimCompletion-Prop.ιA q =
    Real.Base.ElimCompletion-Prop.go (max-assoc-inner p q)
  max-assoc-middle p .Real.Base.ElimCompletion-Prop.limA y gy IH z =
      max-comm (Real.ιℚ p) (Real.Base.lim y gy ⊔ℝ z)
    ∙ cong (_⊔ℝ Real.ιℚ p) (max-lim-left y gy z)
    ∙ max-lim-left (λ n → y n ⊔ℝ z) _ (Real.ιℚ p)
    ∙ lim-cong _ _ (funExt λ n →
        max-comm (y n ⊔ℝ z) (Real.ιℚ p)
      ∙ IH n z
      ∙ cong (_⊔ℝ z) (max-comm (Real.ιℚ p) (y n)))
    ∙ sym (max-lim-left (λ n → y n ⊔ℝ Real.ιℚ p) _ z)
    ∙ cong (_⊔ℝ z) (sym (max-lim-left y gy (Real.ιℚ p)))
    ∙ cong (_⊔ℝ z)
        (sym (max-comm (Real.ιℚ p) (Real.Base.lim y gy)))
  max-assoc-middle p .Real.Base.ElimCompletion-Prop.isPropA y =
    isPropΠ λ z → Real.Base.isSetCompletion _ _

  max-assoc-outer : Real.Base.ElimCompletion-Prop
    (λ x → ∀ y z →
      x ⊔ℝ (y ⊔ℝ z) ≡ (x ⊔ℝ y) ⊔ℝ z)
  max-assoc-outer .Real.Base.ElimCompletion-Prop.ιA p =
    Real.Base.ElimCompletion-Prop.go (max-assoc-middle p)
  max-assoc-outer .Real.Base.ElimCompletion-Prop.limA x gx IH y z =
      max-lim-left x gx (y ⊔ℝ z)
    ∙ lim-cong _ _ (funExt λ n → IH n y z)
    ∙ sym (max-lim-left (λ n → x n ⊔ℝ y) _ z)
    ∙ cong (_⊔ℝ z) (sym (max-lim-left x gx y))
  max-assoc-outer .Real.Base.ElimCompletion-Prop.isPropA x =
    isPropΠ2 λ y z → Real.Base.isSetCompletion _ _


max-assoc : ∀ x y z →
  x ⊔ℝ (y ⊔ℝ z) ≡ (x ⊔ℝ y) ⊔ℝ z
max-assoc = Real.Base.ElimCompletion-Prop.go max-assoc-outer


≤ℝ-trans : ∀ x y z → x ≤ℝ y → y ≤ℝ z → x ≤ℝ z
≤ℝ-trans x y z x≤y y≤z =
    cong (x ⊔ℝ_) (sym y≤z)
  ∙ max-assoc x y z
  ∙ cong (_⊔ℝ z) x≤y
  ∙ y≤z
