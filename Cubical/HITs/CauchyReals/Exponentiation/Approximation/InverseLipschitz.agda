module Cubical.HITs.CauchyReals.Exponentiation.Approximation.InverseLipschitz where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Powerset

open import Cubical.Data.Nat as ℕ hiding (_·_; _+_)
open import Cubical.Data.Rationals as ℚ using (ℚ)
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Closeness
open import Cubical.HITs.CauchyReals.Analysis.Lipschitz.Inverse.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Base hiding (≤Cont₂)
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Order using (≤Cont₂)
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Order.Multiplication using (<ᵣ-o·ᵣ)
open import Cubical.HITs.CauchyReals.Foundation.Rationals

open import Cubical.HITs.CauchyReals.Exponentiation.Approximation.Base

module _ (f : ℚ → ℝ) (B : ℕ → ℚ₊)
  (bl : boundedLipschitz f B) where

  open BoundedLipsch f B bl

  module _ (K : ℕ → ℚ₊) where
    boundedInvLipschitz : Type
    boundedInvLipschitz =
      ∀ n x y
        → abs x ℚ.≤ fromNat (suc n)
        → abs y ℚ.≤ fromNat (suc n)
        → rat (abs (y ℚ.- x)) ≤ᵣ
          rat (fst (K n)) ·ᵣ absᵣ (f y -ᵣ f x)

    module BoundedInvLipsch (ibl : boundedInvLipschitz) where
      opaque
        invLipFₙ : ∀ n → InverseLipschitz-ℝ→ℝℙ (K n)
          (intervalℙ (rat (clampL n)) (rat (clampU n)))
          (λ x _ → fst (fst (flₙ n)) x)
        invLipFₙ n u u∈ v v∈ ε X =
          invEq (∼≃abs<ε _ _ _)
            (isTrans≤<ᵣ _ _ _
              bil-clamp
              (isTrans<≡ᵣ _ _ _
                (<ᵣ-o·ᵣ _ _ (ℚ₊→ℝ₊ (K n))
                  (fst (∼≃abs<ε _ _ _) X))
                (sym (rat·ᵣrat _ _))))
          where
          u' : ℝ
          u' = clampᵣ (rat (clampL n)) (rat (clampU n)) u

          v' : ℝ
          v' = clampᵣ (rat (clampL n)) (rat (clampU n)) v

          opaque
            unfolding _+ᵣ_ maxᵣ
            bil-clamp : absᵣ (u +ᵣ -ᵣ v) ≤ᵣ
              fst (ℚ₊→ℝ₊ (K n)) ·ᵣ
                absᵣ (fst (fst (flₙ n)) u +ᵣ -ᵣ fst (fst (flₙ n)) v)
            bil-clamp =
              subst2 {x = u'} {z = v'}
                (λ u v → absᵣ (u +ᵣ -ᵣ v) ≤ᵣ
                  fst (ℚ₊→ℝ₊ (K n)) ·ᵣ
                    absᵣ (fst (fst (flₙ n)) u +ᵣ -ᵣ
                      fst (fst (flₙ n)) v))
                (sym (∈ℚintervalℙ→clampᵣ≡
                  (rat (clampL n)) (rat (clampU n)) u (fst u∈ , snd u∈)))
                (sym (∈ℚintervalℙ→clampᵣ≡
                  (rat (clampL n)) (rat (clampU n)) v (fst v∈ , snd v∈)))
                (≤Cont₂
                  {λ u v →
                    absᵣ (clampᵣ (rat (clampL n)) (rat (clampU n)) u -ᵣ
                      clampᵣ (rat (clampL n)) (rat (clampU n)) v)}
                  {λ u v →
                    fst (ℚ₊→ℝ₊ (K n)) ·ᵣ
                      absᵣ (fst (fst (flₙ n))
                        (clampᵣ (rat (clampL n)) (rat (clampU n)) u) -ᵣ
                        fst (fst (flₙ n))
                        (clampᵣ (rat (clampL n)) (rat (clampU n)) v))}
                  (cont∘₂ IsContinuousAbsᵣ
                    (cont₂∘ (contNE₂ sumR)
                      (IsContinuousClamp (fromNeg (suc n)) (fromNat (suc n)))
                      (IsContinuous∘ _ _ IsContinuous-ᵣ
                        (IsContinuousClamp
                          (fromNeg (suc n)) (fromNat (suc n))))))
                  (cont∘₂ (IsContinuous·ᵣL _)
                    (cont∘₂ IsContinuousAbsᵣ
                      (cont₂∘ (contNE₂ sumR)
                        (IsContinuous∘ _ _ (snd (flₙ n))
                          (IsContinuousClamp
                            (fromNeg (suc n)) (fromNat (suc n))))
                        (IsContinuous∘ _ _ IsContinuous-ᵣ
                          (IsContinuous∘ _ _ (snd (flₙ n))
                            (IsContinuousClamp
                              (fromNeg (suc n)) (fromNat (suc n))))))))
                  (λ x y →
                    subst2 _≤ᵣ_
                      (sym (absᵣ-rat _)
                        ∙ cong absᵣ (sym (-ᵣ-rat₂ _ _))
                        ∙ cong₂ (λ x' y' → absᵣ (x' -ᵣ y'))
                          (sym (clampᵣ-rat (clampL n) (clampU n) x))
                          (sym (clampᵣ-rat (clampL n) (clampU n) y)))
                      (cong₂
                        (λ fx fy → rat (fst (K n)) ·ᵣ absᵣ (fx -ᵣ fy))
                        (cong f
                          (ℚ.∈ℚintervalℙ→clam≡ _ _
                            (ℚ.clamp (clampL n) (clampU n) x)
                            (ℚ.clam∈ℚintervalℙ _ _
                              (clampL≤clampU n) x))
                          ∙ sym (flₙ-rat n (ℚ.clamp (clampL n) (clampU n) x))
                          ∙ cong (fst (fst (flₙ n)))
                            (sym (clampᵣ-rat (clampL n) (clampU n) x)))
                        (cong f
                          (ℚ.∈ℚintervalℙ→clam≡ _ _
                            (ℚ.clamp (clampL n) (clampU n) y)
                            (ℚ.clam∈ℚintervalℙ _ _
                              (clampL≤clampU n) y))
                          ∙ sym (flₙ-rat n (ℚ.clamp (clampL n) (clampU n) y))
                          ∙ cong (fst (fst (flₙ n)))
                            (sym (clampᵣ-rat (clampL n) (clampU n) y))))
                      (ibl n
                        (ℚ.clamp (clampL n) (clampU n) y)
                        (ℚ.clamp (clampL n) (clampU n) x)
                        (clampAbs≤ n y)
                        (clampAbs≤ n x)))
                  u v)
