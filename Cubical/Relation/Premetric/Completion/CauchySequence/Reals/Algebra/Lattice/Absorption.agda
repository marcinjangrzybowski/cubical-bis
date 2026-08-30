module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Absorption where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat.Base using (ℕ ; zero)
open import Cubical.Data.Rationals.Base as ℚ
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Negation
  as Neg
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Laws


private
  lim-cong : ∀ {x y : ℕ → Real.ℝ}
    (gx : Real.Base.IsCauchySequence x) (gy : Real.Base.IsCauchySequence y) →
    x ≡ y → Real.Base.lim x gx ≡ Real.Base.lim y gy
  lim-cong {x} {y} gx gy p =
    cong (λ z → Real.Base.lim (fst z) (snd z))
      (Σ≡Prop Real.Base.isPropIsCauchySequence p)


neg-min : ∀ x y →
  Neg.- (x ⊓ℝ y) ≡ (Neg.- x) ⊔ℝ (Neg.- y)
neg-min x y =
  Neg.neg-involutive ((Neg.- x) ⊔ℝ (Neg.- y))

neg-max : ∀ x y →
  Neg.- (x ⊔ℝ y) ≡ (Neg.- x) ⊓ℝ (Neg.- y)
neg-max x y =
  cong Neg.-_
    (cong₂ _⊔ℝ_
      (sym (Neg.neg-involutive x))
      (sym (Neg.neg-involutive y)))

min-assoc : ∀ x y z →
  x ⊓ℝ (y ⊓ℝ z) ≡ (x ⊓ℝ y) ⊓ℝ z
min-assoc x y z =
    cong (λ w → Neg.- ((Neg.- x) ⊔ℝ w)) (neg-min y z)
  ∙ cong Neg.-_ (max-assoc (Neg.- x) (Neg.- y) (Neg.- z))
  ∙ cong (λ w → Neg.- (w ⊔ℝ (Neg.- z))) (sym (neg-min x y))

min-lim-left : ∀ x gx y →
  Real.Base.lim x gx ⊓ℝ y ≡
  Real.Base.lim (λ n → x n ⊓ℝ y) _
min-lim-left x gx y =
  cong Neg.-_
    (max-lim-left (Neg.-_ ∘ x) (Neg.neg-seqWitness gx) (Neg.- y))


private
  constantIsCauchySequence : ∀ x → Real.Base.IsCauchySequence (λ _ → x)
  constantIsCauchySequence x ε =
    ∣ zero , (λ _ _ _ _ → Real.Base.isRefl≈ᶜ x ε) ∣₁

  constant-isLimitSeq : ∀ x →
    Real.Premetric.CompletionTheory.isLimitSeq (λ _ → x) x
  constant-isLimitSeq x ε =
    ∣ zero , (λ _ _ → Real.Base.isRefl≈ᶜ x ε) ∣₁

  lim-constant : ∀ x gx → Real.Base.lim (λ _ → x) gx ≡ x
  lim-constant x gx =
    cong fst
      (Real.Premetric.CompletionTheory.isPropLimitSeq (λ _ → x)
        (Real.Base.lim (λ _ → x) gx , Real.Premetric.lim-isLimitSeq _ gx)
        (x , constant-isLimitSeq x))


-- Absorption is the interaction law that turns the two semilattice
-- operations into genuine joins and meets.  The limit/limit case uses the
-- synchronized max computation so both occurrences of the input advance
-- together.

private
 opaque
  max-absorb-min-base : ∀ p → Real.Base.ElimCompletion-Prop
    (λ y → Real.ιℚ p ⊔ℝ (Real.ιℚ p ⊓ℝ y) ≡ Real.ιℚ p)
  max-absorb-min-base p .Real.Base.ElimCompletion-Prop.ιA q =
      cong (Real.ιℚ p ⊔ℝ_) (min-ι p q)
    ∙ max-ι p (ℚ.min p q)
    ∙ cong Real.ιℚ (ℚ.maxAbsorbLMin p q)
  max-absorb-min-base p .Real.Base.ElimCompletion-Prop.limA y gy IH =
      cong (Real.ιℚ p ⊔ℝ_) (min-comm (Real.ιℚ p) (Real.Base.lim y gy))
    ∙ cong (Real.ιℚ p ⊔ℝ_) (min-lim-left y gy (Real.ιℚ p))
    ∙ max-comm (Real.ιℚ p) (Real.Base.lim (λ n → y n ⊓ℝ Real.ιℚ p) _)
    ∙ max-lim-left (λ n → y n ⊓ℝ Real.ιℚ p) _ (Real.ιℚ p)
    ∙ lim-cong _ (constantIsCauchySequence (Real.ιℚ p))
        (funExt λ n →
            max-comm (y n ⊓ℝ Real.ιℚ p) (Real.ιℚ p)
          ∙ cong (Real.ιℚ p ⊔ℝ_) (min-comm (y n) (Real.ιℚ p))
          ∙ IH n)
    ∙ lim-constant (Real.ιℚ p) (constantIsCauchySequence (Real.ιℚ p))
  max-absorb-min-base p .Real.Base.ElimCompletion-Prop.isPropA y =
    Real.Base.isSetCompletion _ _

  max-absorb-min-elim : Real.Base.ElimCompletion-Prop
    (λ x → ∀ y → x ⊔ℝ (x ⊓ℝ y) ≡ x)
  max-absorb-min-elim .Real.Base.ElimCompletion-Prop.ιA p =
    Real.Base.ElimCompletion-Prop.go (max-absorb-min-base p)
  max-absorb-min-elim .Real.Base.ElimCompletion-Prop.limA x gx IH y =
      cong (Real.Base.lim x gx ⊔ℝ_) (min-lim-left x gx y)
    ∙ max-lim-lim x gx (λ n → x n ⊓ℝ y) _
    ∙ lim-cong _ gx (funExt λ n → IH n y)
  max-absorb-min-elim .Real.Base.ElimCompletion-Prop.isPropA x =
    isPropΠ λ y → Real.Base.isSetCompletion _ _


opaque
 max-absorb-min : ∀ x y → x ⊔ℝ (x ⊓ℝ y) ≡ x
 max-absorb-min = Real.Base.ElimCompletion-Prop.go max-absorb-min-elim

 min-absorb-max : ∀ x y → x ⊓ℝ (x ⊔ℝ y) ≡ x
 min-absorb-max x y =
     cong (λ w → Neg.- ((Neg.- x) ⊔ℝ w)) (neg-max x y)
   ∙ cong Neg.-_ (max-absorb-min (Neg.- x) (Neg.- y))
   ∙ Neg.neg-involutive x
