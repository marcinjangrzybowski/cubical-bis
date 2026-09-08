{-# OPTIONS --safe --cubical #-}

module Cubical.HITs.CauchyReals.Example.Financial.Broker2.Pipeline.Receipts where

open import Cubical.HITs.CauchyReals.Example.Financial.Core.Finite
open import Cubical.HITs.CauchyReals.Foundation.Rationals using (ℚ; module ℚ)
open import Cubical.Data.Bool.Base using (Bool; true; false; _or_; _and_; not)
open import Cubical.Data.List.Base using ([]; _∷_; map)
open import Cubical.Data.FinData.Properties using (discreteFin)
import Cubical.Data.FinData.Base as F
open import Cubical.Relation.Nullary using (yes; no)
open import Agda.Builtin.String using (String)
open import Cubical.Experiments.Relation.Base using
  (Fields; Fields'; Row'; Relation; [_; _∶_,_; _∶_]; []; _,,_; _⟩)
import Cubical.Experiments.Relation.Operations as Ops
import Cubical.Experiments.Relation.Aggregation as Aggregation
import Cubical.HITs.CauchyReals.Example.Financial.Broker.Stage05Journal as Receipts

module SumQ = Aggregation.Sum ℚ 0 ℚ._+_

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

  Receipt : Fields
  Receipt = [ "receiptId" ∶ Fin events , "clientId" ∶ Fin clients ,
    "amount" ∶ ℚ , "externalReceiptId" ∶ String ]

  Delivery : Fields
  Delivery = [ "receiptId" ∶ Fin events , "deliveryId" ∶ String ]

  ReceiptRow DeliveryRow : Type₁
  ReceiptRow = Row' (Fields.fields Receipt)
  DeliveryRow = Row' (Fields.fields Delivery)

  Deliveries : Type₁
  Deliveries = Relation Delivery

  receiptId : ReceiptRow → Fin events
  receiptId (event ,, client ,, amount ,, reference ⟩) = event

  clientId : ReceiptRow → Fin clients
  clientId (event ,, client ,, amount ,, reference ⟩) = client

  receiptAmount : ReceiptRow → ℚ
  receiptAmount (event ,, client ,, amount ,, reference ⟩) = amount

  deliveryReceiptId : DeliveryRow → Fin events
  deliveryReceiptId (event ,, delivery ⟩) = event

  catalogRow : Fin events → ReceiptRow
  catalogRow event = event ,, Receipts.owner catalog event ,, Receipts.eventAmount catalog event ,, receiptRef event ⟩

  catalogRows : Relation Receipt
  catalogRows = Ops.tabulateᵣ catalogRow

  decodeBatch : Deliveries → Journal.Batch
  decodeBatch = map deliveryReceiptId

  masks : Deliveries → Journal.Ledger
  masks deliveries = Journal.batchMask (decodeBatch deliveries)

  -- A ledger selects canonical receipt rows once by internal receipt ID.
  -- Repeated delivery rows are never summed as independent cash receipts.
  balanceRows : Journal.Ledger → Relation Receipt
  balanceRows ledger = Ops.selectᵣ (λ row → ledger (receiptId row)) catalogRows

  balances : Journal.Ledger → Fin clients → ℚ
  balances ledger = SumQ.groupSum clientId receiptAmount (balanceRows ledger)

  private
    selected-contribution : ∀ ledger client event →
      SumQ.selected (λ row → ledger (receiptId row)) (SumQ.atKey clientId receiptAmount client) (catalogRow event)
        ≡ contribution catalog ledger client event
    selected-contribution ledger client event with ledger event | discreteFin (Receipts.owner catalog event) client
    ... | false | _ = refl
    ... | true | yes same = refl
    ... | true | no different = refl

  balances-refine-paid : ∀ ledger client → balances ledger client ≡ Journal.paid ledger client
  balances-refine-paid ledger client =
    SumQ.sum-select ℚ.+IdL (λ row → ledger (receiptId row))
      (SumQ.atKey clientId receiptAmount client) catalogRows
    ∙ SumQ.sum-tabulate (SumQ.selected (λ row → ledger (receiptId row))
        (SumQ.atKey clientId receiptAmount client)) catalogRow
    ∙ cong SumQ.finiteSum (funExt (selected-contribution ledger client))
    ∙ finite-paid catalog ledger client

  deltaMask : Journal.Ledger → Deliveries → Journal.Ledger
  deltaMask ledger deliveries event = masks deliveries event and not (ledger event)

  deltaRows : Journal.Ledger → Deliveries → Relation Receipt
  deltaRows ledger deliveries = balanceRows (deltaMask ledger deliveries)

  deltaBalances : Journal.Ledger → Deliveries → Fin clients → ℚ
  deltaBalances ledger deliveries = SumQ.groupSum clientId receiptAmount (deltaRows ledger deliveries)

  deltaBalances-refine-newlyPaid : ∀ ledger deliveries client →
    deltaBalances ledger deliveries client ≡ Journal.newlyPaid ledger (decodeBatch deliveries) client
  deltaBalances-refine-newlyPaid ledger deliveries client =
    balances-refine-paid (deltaMask ledger deliveries) client

  balances-nonnegative : ∀ ledger client → 0 ℚ.≤ balances ledger client
  balances-nonnegative ledger client = subst (0 ℚ.≤_) (sym (balances-refine-paid ledger client))
    (Journal.paid-nonnegative ledger client)

  deltaBalances-nonnegative : ∀ ledger deliveries client → 0 ℚ.≤ deltaBalances ledger deliveries client
  deltaBalances-nonnegative ledger deliveries client = balances-nonnegative (deltaMask ledger deliveries) client

  receiveLedger : Journal.Ledger → Deliveries → Journal.Ledger
  receiveLedger ledger deliveries event = masks deliveries event or ledger event

  receiveLedger-refines-journal : ∀ ledger deliveries →
    receiveLedger ledger deliveries ≡ Journal.ingestBatch ledger (decodeBatch deliveries)
  receiveLedger-refines-journal ledger deliveries = sym (Journal.ingestBatch-closed ledger (decodeBatch deliveries))

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
