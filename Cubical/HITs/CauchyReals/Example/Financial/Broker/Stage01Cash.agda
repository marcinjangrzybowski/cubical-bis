{-# OPTIONS --safe --cubical #-}

-- Stage 1: one signed replacement claim and actually available cash.
-- Financial motivation: REFERENCES.md#bcbs-fx-2013, section 3.3.
module Cubical.HITs.CauchyReals.Example.Financial.Broker.Stage01Cash where

open import Cubical.HITs.CauchyReals.Example.Financial.Core.Finite public
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.Shortfall
import Cubical.HITs.CauchyReals.Example.Financial.Margin.Base as Finite
open import Cubical.Foundations.Equiv using (_≃_; propBiimpl→Equiv)
open import Cubical.Foundations.Univalence using (ua)

record Account : Type₀ where
  constructor account
  field
    claim cash : ℝ
    cash-nonnegative : 0 ≤ᵣ cash
open Account public

Covered : Account → Type₀
Covered a = claim a ≤ᵣ cash a

call : Account → ℝ
call a = stopLoss (claim a) (cash a)

call-nonnegative : ∀ a → 0 ≤ᵣ call a
call-nonnegative a = stopLoss-nonnegative (claim a) (cash a)

-- Issuing a call computes an amount. Only receive changes collateral.
receive : Account → (paid : ℝ) → 0 ≤ᵣ paid → Account
receive a paid paid₊ = account (claim a) (cash a +ᵣ paid)
  (nonnegative-add (cash a) paid (cash-nonnegative a) paid₊)

call-sufficient : ∀ a → Covered (receive a (call a) (call-nonnegative a))
call-sufficient a = stopLoss-reconstruct (claim a) (cash a)

call-least : ∀ a paid paid₊ → Covered (receive a paid paid₊) → call a ≤ᵣ paid
call-least a paid paid₊ = stopLoss-upper (claim a) (cash a) paid paid₊

call-bound→covered : ∀ a paid paid₊ → call a ≤ᵣ paid → Covered (receive a paid paid₊)
call-bound→covered a paid paid₊ bound = isTrans≤ᵣ _ _ _ (call-sufficient a)
  (≤ᵣ-o+ _ _ (cash a) bound)

call-budget≃covered : ∀ a paid paid₊ →
  (call a ≤ᵣ paid) ≃ Covered (receive a paid paid₊)
call-budget≃covered a paid paid₊ = propBiimpl→Equiv (isProp≤ᵣ _ _) (isProp≤ᵣ _ _)
  (call-bound→covered a paid paid₊) (call-least a paid paid₊)

call-policy-path : ∀ a paid paid₊ →
  (call a ≤ᵣ paid) ≡ Covered (receive a paid paid₊)
call-policy-path a paid paid₊ = ua (call-budget≃covered a paid paid₊)

remaining-call : ∀ a paid paid₊ → call (receive a paid paid₊) ≡ stopLoss (call a) paid
remaining-call a paid paid₊ =
  Finite.margin-postCash {0} (λ _ → claim a) (λ _ → cash a) paid paid₊

-- Evidence of nonnegativity does not distinguish accounts with the same
-- claim and cash. This makes state-update composition an actual path.
account-path : ∀ a b → claim a ≡ claim b → cash a ≡ cash b → a ≡ b
account-path a b claims balances i .claim = claims i
account-path a b claims balances i .cash = balances i
account-path a b claims balances i .cash-nonnegative =
  isProp→PathP (λ j → isProp≤ᵣ 0 (balances j)) (cash-nonnegative a) (cash-nonnegative b) i

receive-zero : ∀ a → receive a 0 (≤ᵣ-refl 0) ≡ a
receive-zero a = account-path _ _ refl (+IdR (cash a))

receive-compose : ∀ a p q p₊ q₊ →
  receive (receive a p p₊) q q₊ ≡ receive a (p +ᵣ q) (nonnegative-add p q p₊ q₊)
receive-compose a p q p₊ q₊ = account-path _ _ refl (sym (+ᵣAssoc (cash a) p q))
