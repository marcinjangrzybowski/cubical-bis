{-# OPTIONS --safe --cubical #-}

-- Stage 3: any finite collection of separately authorized netting sets.
-- REFERENCES.md#bcbs-fx-2013 explains the financial separation; no client
-- claim is offset against a different client's collateral or negative mark.
module Cubical.HITs.CauchyReals.Example.Financial.Broker.Stage03NettingSets where

open import Cubical.HITs.CauchyReals.Example.Financial.Core.Finite
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.Shortfall
open import Cubical.HITs.CauchyReals.Foundation.Rationals using (ℚ; module ℚ)
open import Cubical.Relation.Nullary using (Dec; yes; no; ¬_)
open import Cubical.Data.FinData.Properties using (∀Dec)
open import Cubical.Data.Sum.Base using (inl; inr)
import Cubical.Data.Empty as Empty
import Cubical.HITs.CauchyReals.Example.Financial.Broker.Stage02Scenarios as Scenarios
import Cubical.HITs.CauchyReals.Example.Financial.Margin.CounterpartyRisk as Credit

module NettingSets {clients : ℕ} {State : Type₀} (Allowed : State → Type₀)
  (claims collateral : State → Vector clients) where

  module Client (client : Fin clients) = Scenarios.ScenarioAccount Allowed
    (λ state → claims state client) (λ state → collateral state client)

  Reports : Type₀
  Reports = ∀ client → Client.Report client

  Payments : Type₀
  Payments = Fin clients → ℚ

  Nonnegative : Payments → Type₀
  Nonnegative paid = ∀ client → 0 ℚ.≤ paid client

  posted : Payments → State → Vector clients
  posted paid state client = collateral state client +ᵣ rat (paid client)

  Covered : Payments → Type₀
  Covered paid = ∀ state → Allowed state → ∀ client → claims state client ≤ᵣ posted paid state client

  upperCalls lowerCalls : Reports → Payments
  upperCalls reports client = Client.upper (reports client)
  lowerCalls reports client = Client.lower (reports client)

  upperCalls-nonnegative : ∀ reports → Nonnegative (upperCalls reports)
  upperCalls-nonnegative reports client = Client.upper-nonnegative (reports client)

  upperCalls-cover : ∀ reports → Covered (upperCalls reports)
  upperCalls-cover reports state member client = Client.upper-covers (reports client) state member

  record BookGuarantee (paid : Payments) : Type₀ where
    field
      all-covered : Covered paid
      residual-zero : ∀ state → Allowed state → Credit.brokerResidual (claims state) (posted paid state) ≡ 0
      every-loss-zero : (severity : State → Credit.Severity clients) → ∀ state → Allowed state →
        Credit.realizedCloseoutLoss (claims state) (posted paid state) (severity state) ≡ 0
  open BookGuarantee public

  guarantee : ∀ paid → Covered paid → BookGuarantee paid
  guarantee paid coverage .all-covered = coverage
  guarantee paid coverage .residual-zero state member = sum-cong _ (λ _ → 0)
    (λ client → stopLoss-zero-below (claims state client) (posted paid state client)
      (coverage state member client)) ∙ sum-zero clients
  guarantee paid coverage .every-loss-zero severity state member =
    Credit.covered-loss-zero (claims state) (posted paid state) (severity state) (coverage state member)

  -- A collective assessment preserves the distinction between a refuted
  -- obligation and an inconclusive enclosure. It checks every lower bound
  -- before returning an inconclusive result, even if some upper bound fails.
  data Assessment (reports : Reports) (paid : Payments) : Type₀ where
    covered : BookGuarantee paid → Assessment reports paid
    deficient : (client : Fin clients) → ¬ Client.Coverage client (rat (paid client)) → Assessment reports paid
    inconclusive : (∀ client → lowerCalls reports client ℚ.≤ paid client) →
      (client : Fin clients) → ¬ (upperCalls reports client ℚ.≤ paid client) → Assessment reports paid

  assess : ∀ reports paid → Nonnegative paid → Assessment reports paid
  assess reports paid paid₊ with ∀Dec (λ client → upperCalls reports client ℚ.≤ paid client)
    (λ client → ℚ.≤Dec (upperCalls reports client) (paid client))
  ... | inl bounds = covered (guarantee paid
    (λ state member client → Client.upper-bound→coverage client (reports client) (paid client)
      (bounds client) state member))
  ... | inr (candidate , not-upper) with ∀Dec (λ client → lowerCalls reports client ℚ.≤ paid client)
    (λ client → ℚ.≤Dec (lowerCalls reports client) (paid client))
  ...   | inl lower-bounds = inconclusive lower-bounds candidate not-upper
  ...   | inr (client , not-lower) = deficient client (λ coverage → not-lower
    (Client.coverage→lower-bound client (reports client) (paid client) (paid₊ client) coverage))

  -- If every enclosure collapses to an exact rational value, the entire
  -- book assessment is a complete coverage decision, for any client count.
  decide-exact : ∀ reports → (∀ client → lowerCalls reports client ≡ upperCalls reports client) →
    ∀ paid → Nonnegative paid → Dec (Covered paid)
  decide-exact reports tight paid paid₊ with assess reports paid paid₊
  ... | covered certificate = yes (all-covered certificate)
  ... | deficient client not-covered = no (λ coverage → not-covered (λ state member → coverage state member client))
  ... | inconclusive lower-bounds client not-upper = Empty.rec
    (not-upper (subst (λ q → q ℚ.≤ paid client) (tight client) (lower-bounds client)))

  -- Necessary cash is summed only after proving each netting-set obligation.
  -- Competitors may provide arbitrary nonnegative real cash amounts.
  necessary-total : ∀ reports (paid : Vector clients) → (∀ client → 0 ≤ᵣ paid client) →
    (∀ state → Allowed state → ∀ client → claims state client ≤ᵣ collateral state client +ᵣ paid client) →
    sum (λ client → rat (lowerCalls reports client)) ≤ᵣ sum paid
  necessary-total reports paid paid₊ coverage = sum-monotone _ _
    (λ client → Client.lower-required (reports client) (paid client) (paid₊ client)
      (λ state member → coverage state member client))
