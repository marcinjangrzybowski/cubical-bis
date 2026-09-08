{-# OPTIONS --safe --cubical #-}

module Cubical.HITs.CauchyReals.Example.Financial.Portfolio.ExecutionEquivalence where

open import Cubical.HITs.CauchyReals.Example.Financial.Portfolio.Base public
open import Cubical.HITs.CauchyReals.Example.Financial.Core.EconomicEquivalence
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.RiskLaws
open import Cubical.HITs.CauchyReals.Algebra.Order.AbsoluteValue using (absᵣNonNeg)
open import Cubical.HITs.CauchyReals.Algebra.Order.Properties using (isIrrefl<ᵣ)
open import Cubical.Foundations.Equiv
open import Cubical.Data.Empty using (⊥)
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
import Cubical.Data.FinData.Base as F
import Cubical.HITs.SetQuotients as SQ
import Cubical.HITs.CauchyReals.Example.Financial.Portfolio.TransactionCosts as TC

private
  cancel-added-loss : ∀ a b x → a +ᵣ x ≡ b +ᵣ x → a ≡ b
  cancel-added-loss a b x p =
    sym (cancel a x) ∙ cong (_-ᵣ x) p ∙ cancel b x
    where
    cancel : ∀ y z → (y +ᵣ z) -ᵣ z ≡ y
    cancel y z = ℝ!

-- Fix the starting holdings and execution rates before taking economic
-- classes. There is at least one scenario at which a constant fee can be
-- recovered; with an empty scenario space every loss profile is equal.
module ExecutionModel {m n : ℕ} (M : Market m (suc n)) (rates old : Vector m) where
  module Raw = EconomicModel (Fin (suc n)) (Vector m) (portfolioLoss M)
  module Net = EconomicModel (Fin (suc n)) (Vector m) (TC.allInLoss M rates old)

  cost : Vector m → ℝ
  cost = TC.transactionCost rates old

  equal-costs-preserve-execution : ∀ u v → u Raw.≈ᴱ v → cost u ≡ cost v → u Net.≈ᴱ v
  equal-costs-preserve-execution u v sameRaw sameCost i = cong₂ _+ᵣ_ sameCost (sameRaw i)

  execution-equality-implies-equal-costs : ∀ u v → u Raw.≈ᴱ v → u Net.≈ᴱ v → cost u ≡ cost v
  execution-equality-implies-equal-costs u v sameRaw sameNet =
    cancel-added-loss (cost u) (cost v) (portfolioLoss M u F.zero)
      (sameNet F.zero ∙ cong (cost v +ᵣ_) (sym (sameRaw F.zero)))

  execution-equivalence≃equal-costs : ∀ u v → u Raw.≈ᴱ v →
    (u Net.≈ᴱ v) ≃ (cost u ≡ cost v)
  execution-equivalence≃equal-costs u v sameRaw = propBiimpl→Equiv
    (Net.isPropEconomicEquivalence u v) (isSetℝ _ _)
    (execution-equality-implies-equal-costs u v sameRaw)
    (equal-costs-preserve-execution u v sameRaw)

  execution-class-path≃equal-costs : ∀ u v → u Raw.≈ᴱ v →
    (Net.class u ≡ Net.class v) ≃ (cost u ≡ cost v)
  execution-class-path≃equal-costs u v sameRaw = compEquiv
    (Net.class-path≃economic u v) (execution-equivalence≃equal-costs u v sameRaw)

  -- A sufficient condition for passing from raw economic classes to
  -- execution classes is that the fee itself respects raw equivalence.
  CostInvariant : Type₀
  CostInvariant = ∀ u v → u Raw.≈ᴱ v → cost u ≡ cost v

  execution-descends : CostInvariant → Raw.EconomicClass → Net.EconomicClass
  execution-descends invariant = SQ.rec Net.isSetEconomicClass Net.class
    (λ u v sameRaw → Net.class-sound (equal-costs-preserve-execution u v sameRaw
      (invariant u v sameRaw)))

  execution-descends-β : ∀ invariant u → execution-descends invariant (Raw.class u) ≡ Net.class u
  execution-descends-β invariant u = refl

  -- The condition is necessary as well: a quotient map which agrees on
  -- representatives would identify their execution classes and hence fees.
  execution-descent-implies-cost-invariant :
    (f : Raw.EconomicClass → Net.EconomicClass) →
    (∀ u → f (Raw.class u) ≡ Net.class u) → CostInvariant
  execution-descent-implies-cost-invariant f agrees u v sameRaw =
    execution-equality-implies-equal-costs u v sameRaw
      (Net.class-effective (sym (agrees u)
        ∙ cong f (Raw.class-sound sameRaw) ∙ agrees v))
