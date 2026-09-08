{-# OPTIONS --safe --cubical #-}

module Cubical.HITs.CauchyReals.Example.Financial.Broker2.Pipeline.Properties.Receipts where

open import Cubical.HITs.CauchyReals.Example.Financial.Core.Finite
open import Cubical.HITs.CauchyReals.Foundation.Rationals using (ℚ; module ℚ)
open import Cubical.Data.Bool.Base using (Bool; true; false; _or_; _and_; not)
open import Cubical.Data.List.Base using ([]; _∷_; map)
open import Cubical.Data.FinData.Properties using (discreteFin)
import Cubical.Data.FinData.Base as F
open import Cubical.Relation.Nullary using (yes; no)
open import Agda.Builtin.String using (String)
open import Cubical.Experiments.Relation.Base using
  ([]; _,,_; _⟩)
import Cubical.Experiments.Relation.Operations as Ops
import Cubical.HITs.CauchyReals.Example.Financial.Broker2.Pipeline.Implementation.Receipts as Implementation
import Cubical.HITs.CauchyReals.Example.Financial.Broker.Stage05Journal as Receipts

module SumQ = Implementation.SumQ

private
  -- A single-key catalog exposes the journal's finite fold without changing
  -- its private implementation. Arbitrary client attribution is supplied as
  -- the value vector, after the fixed key has reduced.
  mark : Bool → ℚ → ℚ
  mark false value = 0
  mark true value = value

  valueCatalog : ∀ {events} (values : Fin events → ℚ) → (∀ event → 0 ℚ.≤ values event) →
    Receipts.EventCatalog events 1
  valueCatalog values positive = Receipts.event-catalog (λ _ → F.zero) values positive

  finite-paid-values : ∀ {events} (values : Fin events → ℚ) positive ledger →
    SumQ.finiteSum (λ event → mark (ledger event) (values event))
      ≡ Receipts.Journal.paid (valueCatalog values positive) ledger F.zero
  finite-paid-values {zero} values positive ledger = refl
  finite-paid-values {suc events} values positive ledger with ledger F.zero
  ... | false = cong (0 ℚ.+_)
    (finite-paid-values (λ event → values (F.suc event)) (λ event → positive (F.suc event))
      (λ event → ledger (F.suc event)))
  ... | true = cong (values F.zero ℚ.+_)
    (finite-paid-values (λ event → values (F.suc event)) (λ event → positive (F.suc event))
      (λ event → ledger (F.suc event)))

  contribution : ∀ {events clients} (catalog : Receipts.EventCatalog events clients) →
    Receipts.Journal.Ledger catalog → Fin clients → Fin events → ℚ
  contribution catalog ledger client event =
    mark (ledger event) (Receipts.Journal.attributedAmount catalog event client)

  finite-paid : ∀ {events clients} (catalog : Receipts.EventCatalog events clients)
    (ledger : Receipts.Journal.Ledger catalog) client →
    SumQ.finiteSum (contribution catalog ledger client) ≡ Receipts.Journal.paid catalog ledger client
  finite-paid catalog ledger client = finite-paid-values
    (λ event → Receipts.Journal.attributedAmount catalog event client)
    (λ event → Receipts.Journal.attributedAmount-nonnegative catalog event client) ledger

-- Internal receipt IDs denote distinct actual eligible cash receipts in the
-- supplied immutable catalog. External receipt/delivery IDs are retained as
-- metadata. Deliveries carry no mutable owner or amount, so replay cannot
-- alter those catalog facts. Their authenticity remains a source assumption.
module RelationalReceipts {events clients : ℕ}
  (catalog : Receipts.EventCatalog events clients) (receiptRef : Fin events → String) where

  module Journal = Receipts.Journal catalog
  open Implementation.RelationalReceipts (Receipts.owner catalog) (Receipts.eventAmount catalog) receiptRef public

  decodeBatch : Deliveries → Journal.Batch
  decodeBatch = map (Ops.get "receiptId")

  masks-refine-batch : ∀ deliveries →
    Ops.keyMask (Ops.get "receiptId") deliveries ≡ Journal.batchMask (decodeBatch deliveries)
  masks-refine-batch [] = refl
  masks-refine-batch (row ∷ rows) = funExt (λ event →
    cong (Journal.eventMask (Ops.get "receiptId" row) event or_)
      (funExt⁻ (masks-refine-batch rows) event))

  private
    -- Local annotations expose the catalog and selected mask in sum proofs;
    -- the runtime program keeps both calculations inside its relation chain.
    catalogRow : Fin events → ReceiptRow
    catalogRow event = event ,, Receipts.owner catalog event ,,
      Receipts.eventAmount catalog event ,, receiptRef event ⟩

    deltaMask : Ledger → Deliveries → Ledger
    deltaMask ledger deliveries event =
      Ops.keyMask (Ops.get "receiptId") deliveries event and not (ledger event)

    selected-contribution : ∀ ledger client event →
      SumQ.selected (λ row → ledger (Ops.get "receiptId" row))
        (SumQ.atKey (Ops.get "clientId") (Ops.get "amount") client) (catalogRow event)
        ≡ contribution catalog ledger client event
    selected-contribution ledger client event with ledger event | discreteFin (Receipts.owner catalog event) client
    ... | false | _ = refl
    ... | true | yes same = refl
    ... | true | no different = refl

  balances-refine-paid : ∀ ledger client → balances ledger client ≡ Journal.paid ledger client
  balances-refine-paid ledger client =
    SumQ.sum-select ℚ.+IdL (λ row → ledger (Ops.get "receiptId" row))
      (SumQ.atKey (Ops.get "clientId") (Ops.get "amount") client) catalogRows
    ∙ SumQ.sum-tabulate (SumQ.selected (λ row → ledger (Ops.get "receiptId" row))
        (SumQ.atKey (Ops.get "clientId") (Ops.get "amount") client)) catalogRow
    ∙ cong SumQ.finiteSum (funExt (selected-contribution ledger client))
    ∙ finite-paid catalog ledger client

  deltaBalances-refine-newlyPaid : ∀ ledger deliveries client →
    deltaBalances ledger deliveries client ≡ Journal.newlyPaid ledger (decodeBatch deliveries) client
  deltaBalances-refine-newlyPaid ledger deliveries client =
    balances-refine-paid (deltaMask ledger deliveries) client
    ∙ cong (λ mask → Journal.paid (λ event → mask event and not (ledger event)) client)
        (masks-refine-batch deliveries)

  balances-nonnegative : ∀ ledger client → 0 ℚ.≤ balances ledger client
  balances-nonnegative ledger client = subst (0 ℚ.≤_) (sym (balances-refine-paid ledger client))
    (Journal.paid-nonnegative ledger client)

  deltaBalances-nonnegative : ∀ ledger deliveries client → 0 ℚ.≤ deltaBalances ledger deliveries client
  deltaBalances-nonnegative ledger deliveries client = balances-nonnegative (deltaMask ledger deliveries) client

  receiveLedger-refines-journal : ∀ ledger deliveries →
    receiveLedger ledger deliveries ≡ Journal.ingestBatch ledger (decodeBatch deliveries)
  receiveLedger-refines-journal ledger deliveries =
    cong (λ mask event → mask event or ledger event) (masks-refine-batch deliveries)
    ∙ sym (Journal.ingestBatch-closed ledger (decodeBatch deliveries))

  -- The received relation refines the journal's exact incremental cash
  -- equation, with both sides computed by relational group aggregation.
  balances-receive-accounting : ∀ ledger deliveries client →
    balances (receiveLedger ledger deliveries) client
      ≡ balances ledger client ℚ.+ deltaBalances ledger deliveries client
  balances-receive-accounting ledger deliveries client =
    balances-refine-paid (receiveLedger ledger deliveries) client
    ∙ cong (λ updated → Journal.paid updated client) (receiveLedger-refines-journal ledger deliveries)
    ∙ Journal.paid-ingestBatch-decomposition ledger (decodeBatch deliveries) client
    ∙ cong₂ ℚ._+_ (sym (balances-refine-paid ledger client))
        (sym (deltaBalances-refine-newlyPaid ledger deliveries client))

  receiveLedger-replay : ∀ ledger deliveries →
    receiveLedger (receiveLedger ledger deliveries) deliveries ≡ receiveLedger ledger deliveries
  receiveLedger-replay ledger deliveries =
    cong (λ updated → receiveLedger updated deliveries) (receiveLedger-refines-journal ledger deliveries)
    ∙ receiveLedger-refines-journal (Journal.ingestBatch ledger (decodeBatch deliveries)) deliveries
    ∙ Journal.ingestBatch-replay ledger (decodeBatch deliveries)
    ∙ sym (receiveLedger-refines-journal ledger deliveries)

  -- Final balances are independent of the order of two delivery relations,
  -- even when either relation contains replay or they share receipt IDs.
  receiveLedger-commutes : ∀ ledger first second →
    receiveLedger (receiveLedger ledger first) second ≡ receiveLedger (receiveLedger ledger second) first
  receiveLedger-commutes ledger first second =
    cong (λ updated → receiveLedger updated second) (receiveLedger-refines-journal ledger first)
    ∙ receiveLedger-refines-journal (Journal.ingestBatch ledger (decodeBatch first)) second
    ∙ Journal.ingestBatch-commutes ledger (decodeBatch first) (decodeBatch second)
    ∙ sym (receiveLedger-refines-journal (Journal.ingestBatch ledger (decodeBatch second)) first)
    ∙ cong (λ updated → receiveLedger updated first) (sym (receiveLedger-refines-journal ledger second))

  balances-receive-commutes : ∀ ledger first second →
    balances (receiveLedger (receiveLedger ledger first) second)
      ≡ balances (receiveLedger (receiveLedger ledger second) first)
  balances-receive-commutes ledger first second = cong balances (receiveLedger-commutes ledger first second)
