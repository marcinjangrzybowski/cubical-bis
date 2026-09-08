{-# OPTIONS --safe --cubical #-}

module Cubical.HITs.CauchyReals.Example.Financial.Risk.WorstCase where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Nat.Literals
open import Cubical.Data.FinData.Base using (Fin; zero; suc)

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Algebra.Order.Lattice
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition.Base
open import Cubical.HITs.CauchyReals.Algebra.Multiplication
open import Cubical.HITs.CauchyReals.Algebra.Order.Multiplication
open import Cubical.HITs.CauchyReals.Analysis.Continuity.Core
open import Cubical.HITs.CauchyReals.Foundation.Rationals using (module ℚ)

-- Positive numbers denote losses. A negative worst loss is a guaranteed gain.
-- The scenario space is inhabited, so no artificial zero enters its maximum.
worstCase : ∀ {n} → (Fin (suc n) → ℝ) → ℝ
worstCase {zero} X = X zero
worstCase {suc n} X = maxᵣ (X zero) (worstCase (X ∘ suc))

worstCase-upper : ∀ {n} (X : Fin (suc n) → ℝ) i →
  X i ≤ᵣ worstCase X
worstCase-upper {zero} X zero = ≤ᵣ-refl _
worstCase-upper {suc n} X zero = ≤maxᵣ _ _
worstCase-upper {suc n} X (suc i) =
  isTrans≤ᵣ _ _ _ (worstCase-upper (X ∘ suc) i)
    (isTrans≤≡ᵣ _ _ _ (≤maxᵣ _ _) (maxᵣComm _ _))

worstCase-least : ∀ {n} (X : Fin (suc n) → ℝ) c →
  (∀ i → X i ≤ᵣ c) → worstCase X ≤ᵣ c
worstCase-least {zero} X c bound = bound zero
worstCase-least {suc n} X c bound =
  max≤-lem _ _ _ (bound zero)
    (worstCase-least (X ∘ suc) c (bound ∘ suc))

-- An explicit attaining scenario certifies an exact finite maximum.
-- No selection of an argmax for arbitrary Cauchy reals is required.
worstCase-exact-at : ∀ {n} (X : Fin (suc n) → ℝ) c i →
  (∀ j → X j ≤ᵣ c) → X i ≡ c → worstCase X ≡ c
worstCase-exact-at X c i upper attained = isAntisym≤ᵣ _ _
  (worstCase-least X c upper)
  (isTrans≡≤ᵣ _ _ _ (sym attained) (worstCase-upper X i))

worstCase-monotone : ∀ {n} (X Y : Fin (suc n) → ℝ) →
  (∀ i → X i ≤ᵣ Y i) → worstCase X ≤ᵣ worstCase Y
worstCase-monotone X Y bound = worstCase-least X _ λ i →
  isTrans≤ᵣ _ _ _ (bound i) (worstCase-upper Y i)

worstCase-constant : ∀ {n} c →
  worstCase {n} (λ _ → c) ≡ c
worstCase-constant {zero} c = refl
worstCase-constant {suc n} c =
  cong (maxᵣ c) (worstCase-constant {n} c) ∙ maxᵣIdem c

-- Adding a certain loss adds exactly that amount of risk.
worstCase-cash : ∀ {n} (X : Fin (suc n) → ℝ) c →
  worstCase (λ i → X i +ᵣ c) ≡ worstCase X +ᵣ c
worstCase-cash {zero} X c = refl
worstCase-cash {suc n} X c =
  cong (maxᵣ (X zero +ᵣ c)) (worstCase-cash (X ∘ suc) c)
  ∙ sym (+ᵣMaxDistr _ _ c)

-- Diversification never exceeds the sum of the separate worst losses.
worstCase-subadditive : ∀ {n} (X Y : Fin (suc n) → ℝ) →
  worstCase (λ i → X i +ᵣ Y i) ≤ᵣ worstCase X +ᵣ worstCase Y
worstCase-subadditive X Y = worstCase-least _ _ λ i →
  ≤ᵣMonotone+ᵣ _ _ _ _ (worstCase-upper X i) (worstCase-upper Y i)

-- Uniform one-sided model error gives the same error on required capital.
worstCase-perturbation : ∀ {n} (X Y : Fin (suc n) → ℝ) ε →
  (∀ i → X i ≤ᵣ Y i +ᵣ ε) →
  worstCase X ≤ᵣ worstCase Y +ᵣ ε
worstCase-perturbation X Y ε bound =
  isTrans≤≡ᵣ _ _ _
    (worstCase-monotone X (λ i → Y i +ᵣ ε) bound)
    (worstCase-cash Y ε)

-- A risk budget and all its scenario obligations are equivalent propositions.
-- Univalence lets a dependent certification interface transport along this
-- equivalence without keeping a chosen proof of any order comparison.
worstCase-budget≃pointwise : ∀ {n} (X : Fin (suc n) → ℝ) budget →
  (worstCase X ≤ᵣ budget) ≃ (∀ i → X i ≤ᵣ budget)
worstCase-budget≃pointwise X budget = propBiimpl→Equiv
  (isProp≤ᵣ _ _) (isPropΠ (λ _ → isProp≤ᵣ _ _))
  (λ p i → isTrans≤ᵣ _ _ _ (worstCase-upper X i) p)
  (worstCase-least X budget)

worstCase-budget-path : ∀ {n} (X : Fin (suc n) → ℝ) budget →
  (worstCase X ≤ᵣ budget) ≡ (∀ i → X i ≤ᵣ budget)
worstCase-budget-path X budget = ua (worstCase-budget≃pointwise X budget)

-- Continuity extends the existing rational scaling theorem to arbitrary
-- nonnegative Cauchy reals, including zero. Clamping the coefficient makes
-- the extension a theorem on all reals and avoids choosing its sign.
max-scale-nonnegative : ∀ x y a → 0 ≤ᵣ a →
  maxᵣ x y ·ᵣ a ≡ maxᵣ (x ·ᵣ a) (y ·ᵣ a)
max-scale-nonnegative x y a a₊ =
  subst (λ z → maxᵣ x y ·ᵣ z ≡ maxᵣ (x ·ᵣ z) (y ·ᵣ z))
    (≤ᵣ→≡ a₊)
    (≡Continuous _ _
      (IsContinuous∘ _ _ (IsContinuous·ᵣL (maxᵣ x y)) (IsContinuousMaxL 0))
      (cont₂maxᵣ _ _
        (IsContinuous∘ _ _ (IsContinuous·ᵣL x) (IsContinuousMaxL 0))
        (IsContinuous∘ _ _ (IsContinuous·ᵣL y) (IsContinuousMaxL 0)))
      (λ q → cong (maxᵣ x y ·ᵣ_) (maxᵣ-rat 0 q)
        ∙ ·ᵣMaxDistrPos x y (ℚ.max 0 q) (ℚ.≤max 0 q)
        ∙ cong₂ maxᵣ
            (cong (x ·ᵣ_) (sym (maxᵣ-rat 0 q)))
            (cong (y ·ᵣ_) (sym (maxᵣ-rat 0 q)))) a)

worstCase-scale-right : ∀ {n} (X : Fin (suc n) → ℝ) a → 0 ≤ᵣ a →
  worstCase (λ i → X i ·ᵣ a) ≡ worstCase X ·ᵣ a
worstCase-scale-right {zero} X a a₊ = refl
worstCase-scale-right {suc n} X a a₊ =
  cong (maxᵣ (X zero ·ᵣ a)) (worstCase-scale-right (X ∘ suc) a a₊)
  ∙ sym (max-scale-nonnegative _ _ a a₊)

worstCase-scale : ∀ {n} (X : Fin (suc n) → ℝ) a → 0 ≤ᵣ a →
  worstCase (λ i → a ·ᵣ X i) ≡ a ·ᵣ worstCase X
worstCase-scale X a a₊ =
  cong worstCase (funExt (λ i → ·ᵣComm a (X i)))
  ∙ worstCase-scale-right X a a₊ ∙ ·ᵣComm _ a

-- This stronger conic inequality includes convexity when a + b = 1.
worstCase-weighted : ∀ {n} (X Y : Fin (suc n) → ℝ) a b →
  0 ≤ᵣ a → 0 ≤ᵣ b →
  worstCase (λ i → a ·ᵣ X i +ᵣ b ·ᵣ Y i)
    ≤ᵣ a ·ᵣ worstCase X +ᵣ b ·ᵣ worstCase Y
worstCase-weighted X Y a b a₊ b₊ = worstCase-least _ _ λ i →
  ≤ᵣMonotone+ᵣ _ _ _ _
    (≤ᵣ-o·ᵣ _ _ a a₊ (worstCase-upper X i))
    (≤ᵣ-o·ᵣ _ _ b b₊ (worstCase-upper Y i))
