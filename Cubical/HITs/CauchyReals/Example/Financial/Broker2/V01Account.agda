{-# OPTIONS --safe --cubical #-}

-- Version 1: determine the additional cash needed to cover one account.
-- State contains a signed replacement claim and nonnegative available cash,
-- measured in the same unit. A positive claim is an amount owed to the broker;
-- Safe means that this claim is no larger than the account's cash.
--
-- quoteCall computes max(claim - cash, 0). This is an incremental amount:
-- existing cash is already included. receive adds a supplied nonnegative
-- receipt to the balance; computing or issuing a quote never changes cash.
--
-- The main contract is receive-correct: for every account and every
-- nonnegative real receipt, meeting the quote makes the resulting state Safe.
-- quote-least proves the converse, and quote-sufficient covers paying exactly
-- the quote. Together they characterize the least additional cash requirement.
-- remaining-quote describes partial payment, while receive-compose identifies
-- two successive receipts with receiving their combined amount.
--
-- This is the baseline for the later client, stress and receipt versions.
-- account-path includes the balance's nonnegativity evidence in state equality.
-- adequate≃safe and policy-path express the contract as an equivalence and a
-- Cubical path. They do not decide arbitrary Cauchy-real comparisons; actual
-- cash availability is the financial interpretation of the supplied state.
module Cubical.HITs.CauchyReals.Example.Financial.Broker2.V01Account where

open import Cubical.HITs.CauchyReals.Example.Financial.Core.Finite public
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.Shortfall
import Cubical.HITs.CauchyReals.Example.Financial.Margin.Base as Margin
open import Cubical.Foundations.Equiv using (_≃_; propBiimpl→Equiv)
open import Cubical.Foundations.Univalence using (ua)

record State : Type₀ where
  constructor account
  field
    claim cash : ℝ
    cash-nonnegative : 0 ≤ᵣ cash
open State public

Safe : State → Type₀
Safe b = claim b ≤ᵣ cash b

quoteCall : State → ℝ
quoteCall b = stopLoss (claim b) (cash b)

-- The argument is received, available cash. Quoting never credits it.
receive : State → (paid : ℝ) → 0 ≤ᵣ paid → State
receive b paid paid₊ = account (claim b) (cash b +ᵣ paid)
  (nonnegative-add (cash b) paid (cash-nonnegative b) paid₊)

quote-nonnegative : ∀ b → 0 ≤ᵣ quoteCall b
quote-nonnegative b = stopLoss-nonnegative (claim b) (cash b)

receive-correct : ∀ b paid paid₊ → quoteCall b ≤ᵣ paid → Safe (receive b paid paid₊)
receive-correct b paid paid₊ enough = isTrans≤ᵣ _ _ _
  (stopLoss-reconstruct (claim b) (cash b)) (≤ᵣ-o+ _ _ (cash b) enough)

quote-least : ∀ b paid paid₊ → Safe (receive b paid paid₊) → quoteCall b ≤ᵣ paid
quote-least b paid paid₊ = stopLoss-upper (claim b) (cash b) paid paid₊

quote-sufficient : ∀ b → Safe (receive b (quoteCall b) (quote-nonnegative b))
quote-sufficient b = receive-correct b (quoteCall b) (quote-nonnegative b) (≤ᵣ-refl (quoteCall b))

remaining-quote : ∀ b paid paid₊ → quoteCall (receive b paid paid₊) ≡ stopLoss (quoteCall b) paid
remaining-quote b paid paid₊ = Margin.margin-postCash {0} (λ _ → claim b) (λ _ → cash b) paid paid₊

-- Equal observable fields identify entire states, including their proofs.
account-path : ∀ left right → claim left ≡ claim right → cash left ≡ cash right → left ≡ right
account-path left right marks balances i .claim = marks i
account-path left right marks balances i .cash = balances i
account-path left right marks balances i .cash-nonnegative =
  isProp→PathP (λ j → isProp≤ᵣ 0 (balances j)) (cash-nonnegative left) (cash-nonnegative right) i

receive-compose : ∀ b p q p₊ q₊ →
  receive (receive b p p₊) q q₊ ≡ receive b (p +ᵣ q) (nonnegative-add p q p₊ q₊)
receive-compose b p q p₊ q₊ = account-path _ _ refl (sym (+ᵣAssoc (cash b) p q))

-- Same policy, two specifications: an amount check or the resulting state.
-- These propositions are equivalent, and Cubical univalence gives a path.
adequate≃safe : ∀ b paid paid₊ → (quoteCall b ≤ᵣ paid) ≃ Safe (receive b paid paid₊)
adequate≃safe b paid paid₊ = propBiimpl→Equiv (isProp≤ᵣ _ _) (isProp≤ᵣ _ _)
  (receive-correct b paid paid₊) (quote-least b paid paid₊)

policy-path : ∀ b paid paid₊ → (quoteCall b ≤ᵣ paid) ≡ Safe (receive b paid paid₊)
policy-path b paid paid₊ = ua (adequate≃safe b paid paid₊)
