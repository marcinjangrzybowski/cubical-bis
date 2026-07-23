module Cubical.HITs.CauchyReals.Algebra.Signs where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Bool as 𝟚 hiding (_≤_)
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Nat as ℕ hiding (_·_; _+_)
open import Cubical.Data.NatPlusOne

open import Cubical.HITs.PropositionalTruncation as PT

import Cubical.Algebra.CommRing.Base as CommRing
import Cubical.Algebra.Ring.Properties as Ring
import Cubical.Algebra.OrderedCommRing.Properties as Ordered

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Core
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Predicate
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition.Strict using
  (≤absᵣ)
open import Cubical.HITs.CauchyReals.Algebra.Order.AbsoluteValue using
  (abs-max)
open import Cubical.HITs.CauchyReals.Algebra.Order.Apartness
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Ring
open import Cubical.HITs.CauchyReals.Algebra.Order.Instance
open import Cubical.HITs.CauchyReals.Foundation.Rationals

open import Cubical.Tactics.CommRingSolver.Specialised.Reals

module ℚ→ℝSigns =
  Ring.RingHomTheory (CommRing.CommRingHom→RingHom ℚ→ℝHom)

module ℝOrder = Ordered.OrderedCommRingTheory ℝOrderedCommRing


signᵣ : ∀ r → 0 ＃ r → ℝ
signᵣ _ = ⊎.rec (λ _ → rat 1) (λ _ → rat -1)


0<signᵣ : ∀ r 0＃r → 0 <ᵣ r → 0 <ᵣ signᵣ r 0＃r
0<signᵣ r (inl x) _ = <ℚ→<ᵣ _ _ ((𝟚.toWitness {Q = ℚ.<Dec 0 1} _))
0<signᵣ r (inr x) y = ⊥.rec (isAsym<ᵣ _ _ x y)


signᵣ-rat : ∀ r p → signᵣ (rat r) p ≡ rat (ℚ.sign r)
signᵣ-rat r (inl x) = cong rat (sym (fst (ℚ.<→sign r) (<ᵣ→<ℚ _ _ x)))
signᵣ-rat r (inr x) = cong rat (sym (snd (snd (ℚ.<→sign r)) (<ᵣ→<ℚ _ _ x)))


-- HoTT Theorem (11.3.47)
opaque
  IsContinuousWithPredSignᵣ : IsContinuousWithPred 0＃ₚ signᵣ
  IsContinuousWithPredSignᵣ u ε =
    ⊎.elim
      (λ 0<u → PT.map (λ (q , 0<q , q<u) →
        ((q , <ᵣ→<ℚ _ _ 0<q)) ,
          λ v v∈P v∼u →
            ⊎.elim
              {C = λ v∈P → signᵣ u (inl 0<u) ∼[ ε ] signᵣ v v∈P}
              (λ _ → refl∼ _ _)
              (⊥.rec ∘ (isAsym<ᵣ 0 v
                (subst2 _<ᵣ_ ℝ! ℝ!
                  (<ᵣMonotone+ᵣ _ _ _ _ (-ᵣ<ᵣ (rat q) _ q<u)
                    (a-b<c⇒a<c+b u v _
                      (isTrans≤<ᵣ (u +ᵣ -ᵣ v) (absᵣ (u +ᵣ -ᵣ v)) _
                        (≤absᵣ (u -ᵣ v))
                        (fst (∼≃abs<ε u v
                          (q , (<ᵣ→<ℚ 0 q 0<q))) v∼u)))))))
              v∈P)
        (denseℚinℝ 0 u 0<u))
      (λ u<0 → PT.map (λ (q , u<q , q<0) →
        (ℚ.- q , (ℚ.minus-< q _ (<ᵣ→<ℚ _ _ q<0))) ,
          λ v v∈P v∼u →
            ⊎.elim
              {C = λ v∈P → signᵣ u (inr u<0) ∼[ ε ] signᵣ v v∈P}
              (⊥.rec ∘ (isAsym<ᵣ v 0
                (subst2 _<ᵣ_ ℝ! (+-ᵣ (rat q))
                  (<ᵣMonotone+ᵣ u _ _ _ u<q
                    (isTrans<≡ᵣ _ _ _
                      (isTrans≤<ᵣ (v -ᵣ u) _ _ (≤absᵣ (v -ᵣ u))
                        (fst (∼≃abs<ε _ _ _) (sym∼ _ _ _ v∼u)))
                      (sym (-ᵣ-rat q)))))))
              (λ _ → refl∼ _ _)
              v∈P)
        (denseℚinℝ u 0 u<0))


sign²=1 : ∀ r 0＃r → signᵣ r 0＃r ·ᵣ signᵣ r 0＃r ≡ 1
sign²=1 r = ⊎.elim
  (λ _ → sym (rat·ᵣrat _ _))
  (λ _ → sym (rat·ᵣrat _ _))


opaque
  unfolding absᵣ

  sign·absᵣ : ∀ r 0＃r → absᵣ r ·ᵣ signᵣ r 0＃r ≡ r
  sign·absᵣ r = ∘diag $
    ≡ContinuousWithPred 0＃ₚ 0＃ₚ isOpenPred0＃ isOpenPred0＃
      (λ r 0＃r → absᵣ r ·ᵣ signᵣ r 0＃r)
      (λ r _ → r)
      (cont₂·ᵣWP 0＃ₚ _ _
        (AsContinuousWithPred 0＃ₚ _ IsContinuousAbsᵣ)
        IsContinuousWithPredSignᵣ)
      (AsContinuousWithPred 0＃ₚ _ IsContinuousId)
      (λ r 0＃r 0＃r' →
        (cong₂ _·ᵣ_ refl (signᵣ-rat r 0＃r) ∙ sym (rat·ᵣrat _ _))
        ∙ cong rat
          (cong (ℚ._· ℚ.sign r) (sym (ℚ.abs'≡abs r)) ∙ ℚ.sign·abs r))
      r


  ·sign-flip≡ : ∀ r 0＃r → absᵣ r ≡ r ·ᵣ signᵣ r 0＃r
  ·sign-flip≡ r 0＃r =
    (sym (Rℝ.·IdR' _ _ (sign²=1 r 0＃r)) ∙ ·ᵣAssoc _ _ _)
    ∙ cong (_·ᵣ signᵣ r 0＃r) (sign·absᵣ r 0＃r)

-1ⁿ : ℕ → ℚ
-1ⁿ = ℚ.-1ⁿ

absᵣ[-1ⁿ]≡1 : ∀ n → absᵣ (rat (-1ⁿ n)) ≡ 1
absᵣ[-1ⁿ]≡1 n = absᵣ-rat _ ∙ cong rat (ℚ.abs[-1ⁿ]≡1 n)

-1ⁿ· : ℕ → ℝ → ℝ
-1ⁿ· = Rℝ.alternate

-1ⁿ·-suc : ∀ n x → -1ⁿ· (suc n) x ≡ -ᵣ (-1ⁿ· n x)
-1ⁿ·-suc = Rℝ.alternate-suc

-1ⁿ·-·2 : ∀ n x → -1ⁿ· (n ℕ.· 2) x ≡ x
-1ⁿ·-·2 = Rℝ.alternate-even

-1ⁿ-suc : ∀ n → rat (-1ⁿ (suc n)) ≡ -ᵣ (rat (-1ⁿ n))
-1ⁿ-suc n = cong rat (ℚ.-1ⁿ-suc n) ∙ sym (-ᵣ-rat _)

-1ⁿ·≡· : ∀ n x → -1ⁿ· n x ≡ rat (-1ⁿ n) ·ᵣ x
-1ⁿ·≡· n x =
  Rℝ.alternate≡alternatingSign· n x
  ∙ cong (_·ᵣ x) (sym (ℚ→ℝSigns.pres-alternatingSign n))

absᵣ∘-1ⁿ· : ∀ n x → absᵣ (-1ⁿ· n x) ≡ absᵣ x
absᵣ∘-1ⁿ· n x =
  abs-max _ ∙ ℝOrder.abs-alternate n x ∙ sym (abs-max x)
