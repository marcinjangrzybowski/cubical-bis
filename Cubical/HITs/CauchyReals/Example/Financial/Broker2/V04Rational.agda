{-# OPTIONS --safe --cubical #-}

-- Version 4: put a decidable rational amount gate around real-valued margin.
-- The market and existing balances remain V03 states. Report b supplies
-- nonnegative rational amounts with a proof that they dominate b's current
-- incremental real quotes. The report's state index connects data and evidence.
--
-- quoteCall returns those amounts. receive embeds new nonnegative rational
-- receipts into the real cash balances. Existing cash is already accounted
-- for in the report; it must not be deducted again. advanceReport subtracts
-- only the new receipt and floors at zero, even after partial payment.
--
-- receive-correct proves all-client, all-scenario coverage after receipts
-- meeting a report. assess decides this rational amount check and returns
-- either coverage evidence or an unmet client quote. A conservative report's
-- failure does not establish that the resulting book is undercollateralized.
--
-- With an Exact witness, adequate≃safe and assessExact recover equivalence
-- and a decision for economic coverage. advanceReport-exact preserves that
-- stronger property. RationalInputs.initialReport computes an exact initial
-- report for arbitrary rational market inputs and rational existing cash.
-- General real inputs still require a supplied certified upper bound.
--
-- receive-refines-V03 identifies the rational receipt transition with V03's
-- real transition. No general comparison procedure for Cauchy reals is assumed,
-- and producing a report or assessing a payment never itself receives cash.
module Cubical.HITs.CauchyReals.Example.Financial.Broker2.V04Rational where

open import Cubical.HITs.CauchyReals.Example.Financial.Core.Finite public
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.Shortfall
open import Cubical.HITs.CauchyReals.Foundation.Rationals using (ℚ; module ℚ)
import Cubical.HITs.CauchyReals.Example.Financial.Broker2.V03Stress as Previous
open import Cubical.Relation.Nullary using (Dec; yes; no; ¬_)
open import Cubical.Data.FinData.Properties using (∀Dec)
open import Cubical.Data.Sum.Base using (inl; inr)
open import Cubical.Foundations.Equiv using (_≃_; propBiimpl→Equiv)
open import Cubical.Foundations.Univalence using (ua)
import Cubical.HITs.CauchyReals.Example.Financial.Risk.WorstCase as Worst
import Cubical.Data.FinData.Base as F

open Previous using
  (State; Market; view; Safe; residual; loss; state-path;
   market-data; state; market; cash; cash-nonnegative;
   claims; collateral; collateral-nonnegative;
   safe-residual-zero; safe-loss-zero) public

Payments : ℕ → Type₀
Payments clients = Fin clients → ℚ

Nonnegative : ∀ {clients} → Payments clients → Type₀
Nonnegative paid = ∀ client → 0 ℚ.≤ paid client

toReal : ∀ {clients} → Payments clients → Vector clients
toReal paid client = rat (paid client)

toReal-nonnegative : ∀ {clients} (paid : Payments clients) → Nonnegative paid →
  Previous.Nonnegative (toReal paid)
toReal-nonnegative paid paid₊ client = ≤ℚ→≤ᵣ 0 (paid client) (paid₊ client)

-- Supplied rational upper bounds do not assume that arbitrary Cauchy-real
-- calls are rational or that their order can be decided.
record Report {clients stresses : ℕ} (b : State clients stresses) : Type₀ where
  field
    amounts : Payments clients
    amounts-nonnegative : Nonnegative amounts
    dominates : ∀ client → Previous.quoteCall b client ≤ᵣ rat (amounts client)
open Report public

quoteCall : ∀ {clients stresses} (b : State clients stresses) → Report b → Payments clients
quoteCall b report = amounts report

-- This transition records newly received, available, eligible domestic cash.
-- Computing a report or assessing an intended payment does not receive it.
receive : ∀ {clients stresses} → State clients stresses → (paid : Payments clients) →
  Nonnegative paid → State clients stresses
receive b paid paid₊ = Previous.receive b (toReal paid) (toReal-nonnegative paid paid₊)

Adequate : ∀ {clients stresses} {b : State clients stresses} → Report b → Payments clients → Type₀
Adequate report paid = ∀ client → amounts report client ℚ.≤ paid client

receive-correct : ∀ {clients stresses} (b : State clients stresses) (report : Report b) paid paid₊ →
  Adequate report paid → Safe (receive b paid paid₊)
receive-correct b report paid paid₊ enough = Previous.receive-correct b
  (toReal paid) (toReal-nonnegative paid paid₊) λ client →
    isTrans≤ᵣ _ _ _ (dominates report client)
      (≤ℚ→≤ᵣ (amounts report client) (paid client) (enough client))

report-covers : ∀ {clients stresses} (b : State clients stresses) (report : Report b) →
  Safe (receive b (amounts report) (amounts-nonnegative report))
report-covers b report = receive-correct b report (amounts report) (amounts-nonnegative report)
  (λ client → ℚ.isRefl≤ (amounts report client))

-- Update against the NEW receipt, not the entire existing cash balance.
-- The residual upper bound may stay conservative after partial payment.
advanceReport : ∀ {clients stresses} (b : State clients stresses) (report : Report b) paid paid₊ →
  Report (receive b paid paid₊)
advanceReport b report paid paid₊ .amounts client = ℚ.max (amounts report client ℚ.- paid client) 0
advanceReport b report paid paid₊ .amounts-nonnegative client =
  ℚ.≤max' (amounts report client ℚ.- paid client) 0
advanceReport b report paid paid₊ .dominates client = isTrans≡≤ᵣ _ _ _
  (Previous.remaining-quote b (toReal paid) (toReal-nonnegative paid paid₊) client)
  (isTrans≤≡ᵣ _ _ _
    (stopLoss-monotone (Previous.quoteCall b client) (rat (amounts report client)) (rat (paid client))
      (dominates report client))
    (stopLoss-rat (amounts report client) (paid client)))

data Assessment {clients stresses : ℕ} (b : State clients stresses) (report : Report b)
  (paid : Payments clients) (paid₊ : Nonnegative paid) : Type₀ where
  covered : Adequate report paid → Safe (receive b paid paid₊) → Assessment b report paid paid₊
  unmet-quote : (client : Fin clients) → ¬ (amounts report client ℚ.≤ paid client) →
    Assessment b report paid paid₊

-- Failure identifies an unmet conservative quote. It does NOT assert that
-- the stressed account remains economically unsafe; the report can overstate
-- its exact incremental requirement.
assess : ∀ {clients stresses} (b : State clients stresses) (report : Report b) paid paid₊ →
  Assessment b report paid paid₊
assess b report paid paid₊ with ∀Dec (λ client → amounts report client ℚ.≤ paid client)
  (λ client → ℚ.≤Dec (amounts report client) (paid client))
... | inl enough = covered enough (receive-correct b report paid paid₊ enough)
... | inr (client , insufficient) = unmet-quote client insufficient

-- Refinement is a path of complete engine states, including proof-bearing
-- nonnegative cash. Existing cash itself may be an arbitrary Cauchy real.
receive-refines-V03 : ∀ {clients stresses} (b : State clients stresses) paid paid₊ →
  receive b paid paid₊ ≡ Previous.receive b (toReal paid) (toReal-nonnegative paid paid₊)
receive-refines-V03 b paid paid₊ = refl

-- Exact reports support economic completeness as an optional stronger API.
Exact : ∀ {clients stresses} {b : State clients stresses} → Report b → Type₀
Exact {b = b} report = ∀ client → Previous.quoteCall b client ≡ rat (amounts report client)

safe→adequate : ∀ {clients stresses} (b : State clients stresses) (report : Report b) → Exact report →
  ∀ paid paid₊ → Safe (receive b paid paid₊) → Adequate report paid
safe→adequate b report exact paid paid₊ safe client = ≤ᵣ→≤ℚ (amounts report client) (paid client)
  (subst (_≤ᵣ rat (paid client)) (exact client)
    (Previous.quote-least b (toReal paid) (toReal-nonnegative paid paid₊) safe client))

adequate≃safe : ∀ {clients stresses} (b : State clients stresses) (report : Report b) → Exact report →
  ∀ paid paid₊ → Adequate report paid ≃ Safe (receive b paid paid₊)
adequate≃safe b report exact paid paid₊ = propBiimpl→Equiv
  (isPropΠ (λ client → ℚ.isProp≤ _ _)) (isPropΠ2 (λ _ _ → isProp≤ᵣ _ _))
  (receive-correct b report paid paid₊) (safe→adequate b report exact paid paid₊)

exact-policy-path : ∀ {clients stresses} (b : State clients stresses) (report : Report b) → Exact report →
  ∀ paid paid₊ → Adequate report paid ≡ Safe (receive b paid paid₊)
exact-policy-path b report exact paid paid₊ = ua (adequate≃safe b report exact paid paid₊)

assessExact : ∀ {clients stresses} (b : State clients stresses) (report : Report b) → Exact report →
  ∀ paid paid₊ → Dec (Safe (receive b paid paid₊))
assessExact b report exact paid paid₊ with assess b report paid paid₊
... | covered enough safe = yes safe
... | unmet-quote client insufficient = no λ safe → insufficient
  (safe→adequate b report exact paid paid₊ safe client)

advanceReport-exact : ∀ {clients stresses} (b : State clients stresses) (report : Report b) → Exact report →
  ∀ paid paid₊ → Exact (advanceReport b report paid paid₊)
advanceReport-exact b report exact paid paid₊ client =
  Previous.remaining-quote b (toReal paid) (toReal-nonnegative paid paid₊) client
  ∙ cong (λ call → stopLoss call (rat (paid client))) (exact client)
  ∙ stopLoss-rat (amounts report client) (paid client)

private
  rationalWorst : ∀ {n} → Payments (suc n) → ℚ
  rationalWorst {zero} values = values F.zero
  rationalWorst {suc n} values = ℚ.max (values F.zero) (rationalWorst (λ i → values (F.suc i)))

  rationalWorst-exact : ∀ {n} (values : Payments (suc n)) →
    Worst.worstCase (toReal values) ≡ rat (rationalWorst values)
  rationalWorst-exact {zero} values = refl
  rationalWorst-exact {suc n} values =
    cong (maxᵣ (rat (values F.zero))) (rationalWorst-exact (λ i → values (F.suc i)))
    ∙ maxᵣ-rat (values F.zero) (rationalWorst (λ i → values (F.suc i)))

-- Rational market inputs compute the initial exact report directly. The
-- factory assumes no concrete scenarios and no external margin oracle.
-- Both scenario collateral and the existing cash enter each gap once.
module RationalInputs {clients stresses : ℕ}
  (X C : Fin (suc stresses) → Payments clients)
  (C₊ : ∀ scenario → Nonnegative (C scenario))
  (paid : Payments clients) (paid₊ : Nonnegative paid) where

  initialState : State clients stresses
  initialState = state
    (market-data (λ scenario → toReal (X scenario)) (λ scenario → toReal (C scenario))
      (λ scenario → toReal-nonnegative (C scenario) (C₊ scenario)))
    (toReal paid) (toReal-nonnegative paid paid₊)

  scenarioGap : Fin (suc stresses) → Payments clients
  scenarioGap scenario client = ℚ.max (X scenario client ℚ.- (C scenario client ℚ.+ paid client)) 0

  initialAmounts : Payments clients
  initialAmounts client = rationalWorst (λ scenario → scenarioGap scenario client)

  initial-quote-exact : ∀ client → Previous.quoteCall initialState client ≡ rat (initialAmounts client)
  initial-quote-exact client = cong Worst.worstCase
    (funExt (λ scenario →
      cong (stopLoss (rat (X scenario client))) (+ᵣ-rat (C scenario client) (paid client))
      ∙ stopLoss-rat (X scenario client) (C scenario client ℚ.+ paid client)))
    ∙ rationalWorst-exact (λ scenario → scenarioGap scenario client)

  initialReport : Report initialState
  initialReport .amounts = initialAmounts
  initialReport .amounts-nonnegative client = ≤ᵣ→≤ℚ 0 (initialAmounts client)
    (isTrans≤≡ᵣ _ _ _ (Previous.quote-nonnegative initialState client) (initial-quote-exact client))
  initialReport .dominates client = ≡ᵣWeaken≤ᵣ _ _ (initial-quote-exact client)

  initialReport-exact : Exact initialReport
  initialReport-exact = initial-quote-exact
