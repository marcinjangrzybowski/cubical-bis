{-# OPTIONS --safe --cubical #-}

-- Version 6: evolve the SAME tolerance engine from amount updates to
-- identified receipt events. A proved state projection connects both APIs.
-- Catalog entries denote distinct actual available cash receipts, separate
-- from base collateral. Their identity/authentication is an external input.
module Cubical.HITs.CauchyReals.Example.Financial.Broker2.V06Receipts where

open import Cubical.HITs.CauchyReals.Example.Financial.Core.Finite public
open import Cubical.HITs.CauchyReals.Foundation.Rationals using (ℚ; module ℚ)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Data.Sigma.Properties using (Σ≡Prop)
import Cubical.HITs.CauchyReals.Example.Financial.Broker2.V05Tolerance as Previous
import Cubical.HITs.CauchyReals.Example.Financial.Broker2.V03Stress as Stress
import Cubical.HITs.CauchyReals.Example.Financial.Broker.Stage05Journal as Events

open Previous using (Payments; Nonnegative; zeroMTA) public
open Events using (EventCatalog) public

module Engine {clients stresses events : ℕ} (catalog : EventCatalog events clients) where
  module Journal = Events.Journal catalog

  record State : Type₀ where
    constructor engine-state
    field
      market : Stress.Market clients stresses
      ledger : Journal.Ledger
  open State public

  view : State → Stress.State clients stresses
  view s = Stress.state (market s) (λ client → rat (Journal.paid (ledger s) client))
    (λ client → ≤ℚ→≤ᵣ 0 _ (Journal.paid-nonnegative (ledger s) client))

  Report : State → Type₀
  Report s = Previous.Report (view s)

  quoteCall : (s : State) → Report s → Payments clients → Payments clients
  quoteCall s report mta = Previous.quoteCall (view s) report mta

  receive : State → Journal.Batch → State
  receive s batch = engine-state (market s) (Journal.ingestBatch (ledger s) batch)

  newCash : State → Journal.Batch → Payments clients
  newCash s batch = Journal.newlyPaid (ledger s) batch

  newCash-nonnegative : ∀ s batch → Nonnegative (newCash s batch)
  newCash-nonnegative s batch = Journal.newlyPaid-nonnegative (ledger s) batch

  -- The commuting square is the reason V05's financial proof can be reused.
  -- The old operation receives NEW cash, never the final aggregate balance.
  receive-refines-V05 : ∀ s batch → view (receive s batch) ≡
    Previous.receive (view s) (newCash s batch) (newCash-nonnegative s batch)
  receive-refines-V05 s batch = Stress.state-path _ _ refl
    (funExt (Journal.paid-ingestBatch-accounting (ledger s) batch))

  Adequate : (s : State) → Report s → Payments clients → Journal.Batch → Type₀
  Adequate s report mta batch = Previous.Adequate (view s) report mta (newCash s batch)

  Guarantee : State → Payments clients → Type₀
  Guarantee s mta = Previous.Guarantee (view s) mta

  receive-correct : ∀ s report mta → Nonnegative mta → ∀ batch →
    Adequate s report mta batch → Guarantee (receive s batch) mta
  receive-correct s report mta mta₊ batch enough =
    subst (λ b → Previous.Guarantee b mta) (sym (receive-refines-V05 s batch))
      (Previous.guarantee _ mta
        (Previous.receive-correct (view s) report mta mta₊
          (newCash s batch) (newCash-nonnegative s batch) enough))

  -- Keep the amount computation visibly rational. Only its bound proof is
  -- transported across the change from event state to amount-based state.
  advanceReport : ∀ s → Report s → ∀ batch → Report (receive s batch)
  advanceReport s report batch .Previous.amounts client =
    ℚ.max (Previous.amounts report client ℚ.- newCash s batch client) 0
  advanceReport s report batch .Previous.amounts-nonnegative client =
    ℚ.≤max' (Previous.amounts report client ℚ.- newCash s batch client) 0
  advanceReport s report batch .Previous.dominates client =
    subst (λ b → Stress.quoteCall b client ≤ᵣ
      rat (ℚ.max (Previous.amounts report client ℚ.- newCash s batch client) 0))
      (sym (receive-refines-V05 s batch))
      (Previous.dominates
        (Previous.advanceReport (view s) report (newCash s batch) (newCash-nonnegative s batch)) client)

  data Assessment (s : State) (report : Report s) (mta : Payments clients) (batch : Journal.Batch) : Type₀ where
    controlled : Adequate s report mta batch → Guarantee (receive s batch) mta → Assessment s report mta batch
    unmet-quote : (client : Fin clients) → ¬ (quoteCall s report mta client ℚ.≤ newCash s batch client) →
      Assessment s report mta batch

  assess : ∀ s report mta → Nonnegative mta → ∀ batch → Assessment s report mta batch
  assess s report mta mta₊ batch with Previous.assess (view s) report mta mta₊
    (newCash s batch) (newCash-nonnegative s batch)
  ... | Previous.controlled enough certificate = controlled enough
    (subst (λ b → Previous.Guarantee b mta) (sym (receive-refines-V05 s batch)) certificate)
  ... | Previous.unmet-quote client insufficient = unmet-quote client insufficient

  -- Even a partial receipt yields a valid updated quote for the next call.
  -- A failed assessment does not roll back cash that was actually received.
  record Processed (s : State) (report : Report s) (mta : Payments clients) (batch : Journal.Batch) : Type₀ where
    field
      next-state : State
      state-correct : next-state ≡ receive s batch
      next-report : Report next-state
      assessment : Assessment s report mta batch
  open Processed public

  process : ∀ s report mta → Nonnegative mta → ∀ batch → Processed s report mta batch
  process s report mta mta₊ batch .next-state = receive s batch
  process s report mta mta₊ batch .state-correct = refl
  process s report mta mta₊ batch .next-report = advanceReport s report batch
  process s report mta mta₊ batch .assessment = assess s report mta mta₊ batch

  zero-mta-safe : ∀ s report batch → Adequate s report zeroMTA batch → Stress.Safe (view (receive s batch))
  zero-mta-safe s report batch enough = subst Stress.Safe (sym (receive-refines-V05 s batch))
    (Previous.zero-mta-safe (view s) report (newCash s batch) (newCash-nonnegative s batch) enough)

  state-path : ∀ s t → market s ≡ market t → ledger s ≡ ledger t → s ≡ t
  state-path s t markets ledgers i .market = markets i
  state-path s t markets ledgers i .ledger = ledgers i

  receive-replay : ∀ s batch → receive (receive s batch) batch ≡ receive s batch
  receive-replay s batch = state-path _ _ refl (Journal.ingestBatch-replay (ledger s) batch)

  receive-commutes : ∀ s first second → receive (receive s first) second ≡ receive (receive s second) first
  receive-commutes s first second = state-path _ _ refl (Journal.ingestBatch-commutes (ledger s) first second)

  -- Cubical equality covers the WHOLE engine state, then lifts to its
  -- dependent safety certificate, regardless of how that proof was rebuilt.
  certified-state-replay : ∀ s batch mta
    (before : Guarantee (receive s batch) mta)
    (after : Guarantee (receive (receive s batch) batch) mta) →
    Path (Σ State (λ t → Guarantee t mta))
      (receive (receive s batch) batch , after) (receive s batch , before)
  certified-state-replay s batch mta before after =
    Σ≡Prop (λ t → Previous.guarantee-isProp (view t) mta) (receive-replay s batch)
