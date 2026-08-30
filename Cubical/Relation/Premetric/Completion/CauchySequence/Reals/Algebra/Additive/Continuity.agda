module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Continuity where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat as ℕ using (ℕ ; zero)
open import Cubical.Data.Nat.Order as ℕO
open import Cubical.Data.Rationals.Base as ℚ
import Cubical.Data.Rationals.Order as ℚO
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ
open OrderedCommRingStr (snd ℚOrderedCommRing)
open OrderedCommRingReasoning ℚOrderedCommRing
open OrderedCommRingTheory ℚOrderedCommRing

open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Instances.Rationals using
  (ℚPremetricSpace)

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Translation
  as Tr
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.Addition
  as Add
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Additive.AdditionLaws

import Cubical.Relation.Premetric.Completion.CauchySequence.Extension.CauchyGraph.Binary
  as BinaryDefinition

private
  module B = BinaryDefinition
    ℚPremetricSpace ℚPremetricSpace ℚPremetricSpace

  additionGraph : ℚ → ℚ → Real.ℝ
  additionGraph p q = Real.ιℚ (Add.rationalAddition p q)


-- A constant sequence is Cauchy radius by radius; no modulus is selected.

private
  constantIsCauchySequence : ∀ x →
    Real.Base.IsCauchySequence (λ _ → x)
  constantIsCauchySequence x ε =
    ∣ zero , (λ _ _ _ _ → Real.Base.isRefl≈ᶜ x ε) ∣₁


addRightSequenceWitness : ∀ x {y} →
  Real.Base.IsCauchySequence y →
  Real.Base.IsCauchySequence (λ n → x Add.+ y n)
addRightSequenceWitness x gy =
  Add.add-diagonalIsCauchySequence
    (constantIsCauchySequence x) gy


-- The graph construction computes judgmentally only on constructor pairs.
-- Graph uniqueness supplies the useful one-sided limit rule for an arbitrary
-- completed value in the other argument.

opaque
  add-lim-right : ∀ x y gy →
    x Add.+ Real.Base.lim y gy ≡
    Real.Base.lim (λ n → x Add.+ y n)
      (addRightSequenceWitness x gy)
  add-lim-right x y gy =
    B.graphClosureUnique additionGraph
      Add.rationalAddition-preservesCauchyGraphs
      x (Real.Base.lim y gy)
      (x Add.+ Real.Base.lim y gy)
      (Real.Base.lim (λ n → x Add.+ y n)
        (addRightSequenceWitness x gy))
      (Add.addition-joint x (Real.Base.lim y gy))
      (B.limitRightGraphClosure additionGraph x y gy
        (λ n → x Add.+ y n) (addRightSequenceWitness x gy)
        (λ n → Add.addition-joint x (y n)))


private
  lim-cong : ∀ {x y : ℕ → Real.ℝ}
    (gx : Real.Base.IsCauchySequence x)
    (gy : Real.Base.IsCauchySequence y) →
    x ≡ y → Real.Base.lim x gx ≡ Real.Base.lim y gy
  lim-cong {x} {y} gx gy p =
    cong (λ z → Real.Base.lim (fst z) (snd z))
      (Σ≡Prop Real.Base.isPropIsCauchySequence p)

  translateAsAddElim : ∀ c → Real.Base.ElimCompletion-Prop
    (λ x → Tr.translate c x ≡ x Add.+ Real.ιℚ c)
  translateAsAddElim c .Real.Base.ElimCompletion-Prop.ιA q =
      Tr.translate-ι c q
    ∙ sym (Add.add-ι-ι q c)
  translateAsAddElim c .Real.Base.ElimCompletion-Prop.limA x gx IH =
      lim-cong _ _ (funExt IH)
    ∙ sym (Add.add-lim-ι x gx c)
  translateAsAddElim c .Real.Base.ElimCompletion-Prop.isPropA x =
    Real.Base.isSetCompletion _ _


translate-as-add : ∀ c x →
  Tr.translate c x ≡ x Add.+ Real.ιℚ c
translate-as-add c =
  Real.Base.ElimCompletion-Prop.go (translateAsAddElim c)


-- Pointwise closeness at a strictly smaller radius passes to the two limits.
-- The two limit errors consume only half of the available gap.

opaque
  limits-preserve-closeness-below :
    ∀ {x y} (gx : Real.Base.IsCauchySequence x)
      (gy : Real.Base.IsCauchySequence y) δ ε →
    δ <₊ ε →
    (∀ n → x n Real.Base.≈ᶜ[ δ ] y n) →
    Real.Base.lim x gx Real.Base.≈ᶜ[ ε ] Real.Base.lim y gy
  limits-preserve-closeness-below {x} {y} gx gy δ ε δ<ε pointwise =
    PT.rec2 (Real.Base.isProp≈ᶜ _ ε _) close
      (Real.Premetric.lim-isLimitSeq x gx α)
      (Real.Premetric.lim-isLimitSeq y gy α)
    where
    gap : ℚ₊
    gap = [ ε -₊ δ ]⟨ δ<ε ⟩

    α : ℚ₊
    α = gap /4₊

    total : ℚ₊
    total = α +₊ (δ +₊ α)

    total<ε : total <₊ ε
    total<ε =
      subst2 ℚO._<_ ℚ! (minusPlus₊ ε δ)
        (+MonoR< (fst (gap /2₊)) (fst gap) (fst δ)
          (/2₊<id gap))

    close :
      (Σ[ K ∈ ℕ ] (∀ n → K ℕO.≤ n →
        x n Real.Base.≈ᶜ[ α ] Real.Base.lim x gx)) →
      (Σ[ L ∈ ℕ ] (∀ n → L ℕO.≤ n →
        y n Real.Base.≈ᶜ[ α ] Real.Base.lim y gy)) →
      Real.Base.lim x gx Real.Base.≈ᶜ[ ε ] Real.Base.lim y gy
    close (K , x→lim) (L , y→lim) =
      Real.Base.isMonotone≈ᶜ< _ _ total ε total<ε
        (Real.Premetric.tri≈ᶜ
          (Real.Base.lim x gx) (x n) (Real.Base.lim y gy)
          α (δ +₊ α)
          (Real.Base.sym≈ᶜ (x n) (Real.Base.lim x gx) α
            (x→lim n K≤n))
          (Real.Premetric.tri≈ᶜ
            (x n) (y n) (Real.Base.lim y gy) δ α
            (pointwise n) (y→lim n L≤n)))
      where
      n : ℕ
      n = ℕ.max K L

      K≤n : K ℕO.≤ n
      K≤n = ℕO.left-≤-max {m = K} {n = L}

      L≤n : L ℕO.≤ n
      L≤n = ℕO.right-≤-max {n = L} {m = K}


private
  addIsNonExpandingElim : Real.Base.ElimCompletion-Prop
    (λ y → IsNonExpanding
      (Real.ℝPremetricSpace .snd) (Add._+ y)
      (Real.ℝPremetricSpace .snd))
  addIsNonExpandingElim .Real.Base.ElimCompletion-Prop.ιA q
    .IsNonExpanding.pres≈ x x′ ε x∼x′ =
    subst2 (Real.Base._≈ᶜ[ ε ]_)
      (translate-as-add q x) (translate-as-add q x′)
      (Tr.translate-pres≈ q x x′ ε x∼x′)
  addIsNonExpandingElim .Real.Base.ElimCompletion-Prop.limA y gy IH
    .IsNonExpanding.pres≈ x x′ ε x∼x′ =
    PT.rec (Real.Base.isProp≈ᶜ _ ε _) useSmaller
      (Real.Approximation.isRounded≈ᶜ x x′ ε x∼x′)
    where
    useSmaller :
      Σ[ δ ∈ ℚ₊ ] (δ <₊ ε) ×
        (x Real.Base.≈ᶜ[ δ ] x′) →
      (x Add.+ Real.Base.lim y gy) Real.Base.≈ᶜ[ ε ]
        (x′ Add.+ Real.Base.lim y gy)
    useSmaller (δ , δ<ε , x∼δx′) =
      subst2 (Real.Base._≈ᶜ[ ε ]_)
        (sym (add-lim-right x y gy))
        (sym (add-lim-right x′ y gy))
        (limits-preserve-closeness-below
          (addRightSequenceWitness x gy)
          (addRightSequenceWitness x′ gy) δ ε δ<ε
          (λ n → IH n .IsNonExpanding.pres≈ x x′ δ x∼δx′))
  addIsNonExpandingElim .Real.Base.ElimCompletion-Prop.isPropA y =
    isPropIsNonExpanding
      (Real.ℝPremetricSpace .snd) (Add._+ y)
      (Real.ℝPremetricSpace .snd)


addIsNonExpanding₁ : ∀ y →
  IsNonExpanding
    (Real.ℝPremetricSpace .snd) (Add._+ y)
    (Real.ℝPremetricSpace .snd)
addIsNonExpanding₁ =
  Real.Base.ElimCompletion-Prop.go addIsNonExpandingElim


add-pres≈₁ : ∀ x x′ y ε →
  x Real.Base.≈ᶜ[ ε ] x′ →
  (x Add.+ y) Real.Base.≈ᶜ[ ε ] (x′ Add.+ y)
add-pres≈₁ x x′ y ε =
  addIsNonExpanding₁ y .IsNonExpanding.pres≈ x x′ ε


addIsNonExpanding₂ : ∀ x →
  IsNonExpanding
    (Real.ℝPremetricSpace .snd) (x Add.+_)
    (Real.ℝPremetricSpace .snd)
addIsNonExpanding₂ x .IsNonExpanding.pres≈ y y′ ε y∼y′ =
  subst2 (Real.Base._≈ᶜ[ ε ]_)
    (add-comm y x) (add-comm y′ x)
    (add-pres≈₁ y y′ x ε y∼y′)


add-pres≈₂ : ∀ x y y′ ε →
  y Real.Base.≈ᶜ[ ε ] y′ →
  (x Add.+ y) Real.Base.≈ᶜ[ ε ] (x Add.+ y′)
add-pres≈₂ x y y′ ε =
  addIsNonExpanding₂ x .IsNonExpanding.pres≈ y y′ ε


add-pres≈ : ∀ x x′ y y′ ε δ →
  x Real.Base.≈ᶜ[ ε ] x′ →
  y Real.Base.≈ᶜ[ δ ] y′ →
  (x Add.+ y) Real.Base.≈ᶜ[ ε +₊ δ ] (x′ Add.+ y′)
add-pres≈ x x′ y y′ ε δ x∼x′ y∼y′ =
  Real.Premetric.tri≈ᶜ
    (x Add.+ y) (x′ Add.+ y) (x′ Add.+ y′) ε δ
    (add-pres≈₁ x x′ y ε x∼x′)
    (add-pres≈₂ x′ y y′ δ y∼y′)


-- Pointwise addition preserves continuity for maps from any premetric
-- source.  This closure lemma is useful independently of the completion
-- construction and lets finite sums inherit continuity without introducing
-- chosen moduli.

addOfContinuousIsContinuous : ∀ {ℓ ℓ'} {A : Type ℓ}
  (source : PremetricStr ℓ' A)
  (f g : A → Real.ℝ) →
  isContinuous source f (snd Real.ℝPremetricSpace) →
  isContinuous source g (snd Real.ℝPremetricSpace) →
  isContinuous source (λ x → f x Add.+ g x)
    (snd Real.ℝPremetricSpace)
addOfContinuousIsContinuous source f g f-cont g-cont x
  .IsContinuousAt.pres≈ ε =
  PT.map2 combine
    (f-cont x .IsContinuousAt.pres≈ (ε /2₊))
    (g-cont x .IsContinuousAt.pres≈ (ε /2₊))
  where
  combine :
    (Σ[ δf ∈ ℚ₊ ]
      (∀ y → PremetricStr._≈[_]_ source x δf y →
        f x Real.Base.≈ᶜ[ ε /2₊ ] f y)) →
    (Σ[ δg ∈ ℚ₊ ]
      (∀ y → PremetricStr._≈[_]_ source x δg y →
        g x Real.Base.≈ᶜ[ ε /2₊ ] g y)) →
    Σ[ δ ∈ ℚ₊ ]
      (∀ y → PremetricStr._≈[_]_ source x δ y →
        (f x Add.+ g x) Real.Base.≈ᶜ[ ε ]
        (f y Add.+ g y))
  combine (δf , f-close) (δg , g-close) =
    min₊ δf δg , λ y x≈y →
      subst
        (λ ρ → (f x Add.+ g x) Real.Base.≈ᶜ[ ρ ]
          (f y Add.+ g y))
        (ℚ₊≡ (/2+/2≡id (fst ε)))
        (add-pres≈ (f x) (f y) (g x) (g y)
          (ε /2₊) (ε /2₊)
          (f-close y
            (PremetricStr.isMonotone≈≤ source x y
              (min₊ δf δg) δf (min₊≤L δf δg) x≈y))
          (g-close y
            (PremetricStr.isMonotone≈≤ source x y
              (min₊ δf δg) δg (min₊≤R δf δg) x≈y)))
