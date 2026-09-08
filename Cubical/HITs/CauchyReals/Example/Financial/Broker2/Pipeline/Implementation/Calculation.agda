{-# OPTIONS --safe --cubical #-}

-- A complete read-only margin calculation: read the three source tables,
-- aggregate exposure and cash, reduce across stresses, and return call rows.
-- The separate Properties/Calculation module certifies these returned rows.
module Cubical.HITs.CauchyReals.Example.Financial.Broker2.Pipeline.Implementation.Calculation where

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Literals
open import Cubical.HITs.CauchyReals.Foundation.Rationals using (ℚ; module ℚ; fromNatℚ)
open import Cubical.Experiments.Relation.Base using (Fields; [_; _∶_]; ⟦_⟧; _,,_; [])
open import Cubical.Experiments.Relation.Operations
import Cubical.Experiments.Relation.Aggregation as Aggregation
import Cubical.HITs.CauchyReals.Example.Financial.Broker2.Pipeline.Implementation.Sources as Source
import Cubical.HITs.CauchyReals.Example.Financial.Broker2.Pipeline.Implementation.Valuation as ValuationData
import Cubical.HITs.CauchyReals.Example.Financial.Broker2.Pipeline.Implementation.Receipts as ReceiptData
import Cubical.HITs.CauchyReals.Example.Financial.Broker2.Pipeline.Implementation.Margin as Policy

module Sum = Aggregation.Sum ℚ 0 ℚ._+_
module Maximum = Aggregation.Sum ℚ 0 ℚ.max

module MarginCalculation {clients trades instruments lots assets receipts stresses : ℕ}
  (sources : Source.Schema.DataSources clients trades instruments lots assets receipts stresses) where
  open Source.Schema clients trades instruments lots assets receipts stresses
  module Trades = ValuationData.ValuationPipeline sources
  module Receipts = ReceiptData.RelationalReceipts
    (λ id → CashReceipt.clientId (cashReceipt sources id))
    (λ id → CashReceipt.amount (cashReceipt sources id))
    (λ id → CashReceipt.externalReceiptId (cashReceipt sources id))

  private
    ClientKeys ScenarioKeys : Fields
    ClientKeys = [ "clientId" ∶ ClientId ]
    ScenarioKeys = [ "scenarioId" ∶ ScenarioId ]

  calculate : Valuation → Receipts.Ledger → (ClientId → ℚ) → ⟦ MarginCalls ⟧
  calculate valuation seen mta =
    let
      -- The live trade table: enrich with scenario values, then net by client.
      claims : ScenarioId → ClientId → ℚ
      claims = λ scenario →
        Trades.tradeRows
        |> deriveᵣ "replacementClaim" (λ row →
             get "notional" row ℚ.· unitClaim valuation (get "instrumentId" row) scenario)
        |> Sum.groupSum (get "clientId") (get "replacementClaim")

      -- Custody lots: value allocated inventory and aggregate eligible cover.
      collateral : ScenarioId → ClientId → ℚ
      collateral = λ scenario →
        Trades.collateralRows
        |> deriveᵣ "eligibleValue" (λ row →
             get "units" row ℚ.· eligibleUnitValue valuation (get "assetId" row) scenario)
        |> Sum.groupSum (get "clientId") (get "eligibleValue")

      -- Only canonical receipts marked as recorded enter available cash.
      paid : ClientId → ℚ
      paid =
        Receipts.catalogRows
        |> selectᵣ (λ row → seen (get "receiptId" row))
        |> Sum.groupSum (get "clientId") (get "amount")

      -- Net inside each client first; the maximum must cover every stress.
      required : ClientId → ℚ
      required = λ client →
        tabulateᵣ {schema = Fields.fields ScenarioKeys} (λ scenario → scenario ,, [])
        |> deriveᵣ "requiredCash" (λ row → ℚ.max
             (claims (get "scenarioId" row) client ℚ.-
               (collateral (get "scenarioId" row) client ℚ.+ paid client)) 0)
        |> Maximum.sumBy (get "requiredCash")
    in
      tabulateᵣ {schema = Fields.fields ClientKeys} (λ client → client ,, [])
      |> deriveᵣ "incrementalUpper" (λ row → required (get "clientId" row))
      |> deriveᵣ "requestedCash" (λ row →
           Policy.transferAmount (get "incrementalUpper" row) (mta (get "clientId" row)))
      |> projectᵣ {target = Fields.fields MarginCalls} (λ row →
           get "clientId" row ,, clientReference sources (get "clientId" row) ,, snapshotId valuation ,,
           get "incrementalUpper" row ,, mta (get "clientId" row) ,, get "requestedCash" row ,, [])
