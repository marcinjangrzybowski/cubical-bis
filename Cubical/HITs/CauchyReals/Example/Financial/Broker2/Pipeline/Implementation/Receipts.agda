{-# OPTIONS --safe --cubical #-}

-- Receipt calculations over typed relations, independent of the margin model.
-- The catalog fixes ownership and amounts; deliveries select internal keys.
module Cubical.HITs.CauchyReals.Example.Financial.Broker2.Pipeline.Implementation.Receipts where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat.Literals
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.FinData.Base using (Fin)
open import Cubical.Data.Bool.Base using (Bool; _or_; _and_; not)
open import Cubical.HITs.CauchyReals.Foundation.Rationals using (ℚ; module ℚ)
open import Agda.Builtin.String using (String)
open import Cubical.Experiments.Relation.Base using
  (Fields; Row'; Relation; [_; _∶_,_; _∶_]; []; _,,_; _⟩)
import Cubical.Experiments.Relation.Operations as Ops
open Ops using (_|>_)
import Cubical.Experiments.Relation.Aggregation as Aggregation

module SumQ = Aggregation.Sum ℚ 0 ℚ._+_

module RelationalReceipts {events clients : ℕ}
  (owner : Fin events → Fin clients) (amount : Fin events → ℚ)
  (receiptRef : Fin events → String) where

  Ledger : Type₀
  Ledger = Fin events → Bool

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

  catalogRows : Relation Receipt
  catalogRows = Ops.tabulateᵣ (λ event →
    event ,, owner event ,, amount event ,, receiptRef event ⟩)

  -- Select canonical catalog rows once, never sum repeated delivery rows.
  balances : Ledger → Fin clients → ℚ
  balances ledger =
    catalogRows
      |> Ops.selectᵣ (λ row → ledger (Ops.get "receiptId" row))
      |> SumQ.groupSum (Ops.get "clientId") (Ops.get "amount")

  deltaBalances : Ledger → Deliveries → Fin clients → ℚ
  deltaBalances ledger deliveries =
    catalogRows
      |> Ops.selectᵣ (λ row →
        Ops.keyMask (Ops.get "receiptId") deliveries (Ops.get "receiptId" row)
          and not (ledger (Ops.get "receiptId" row)))
      |> SumQ.groupSum (Ops.get "clientId") (Ops.get "amount")

  receiveLedger : Ledger → Deliveries → Ledger
  receiveLedger ledger deliveries event =
    Ops.keyMask (Ops.get "receiptId") deliveries event or ledger event
