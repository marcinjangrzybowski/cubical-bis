{-# OPTIONS --safe --cubical #-}

-- Runtime valuation and grouping over typed relations. Source catalogs
-- produce one row per key; total functional lookup prices each row once.
-- Reference specifications and model proofs live in Properties/Valuation.agda.
module Cubical.HITs.CauchyReals.Example.Financial.Broker2.Pipeline.Implementation.Valuation where

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Literals
open import Cubical.HITs.CauchyReals.Foundation.Rationals using (ℚ; module ℚ)
open import Cubical.Experiments.Relation.Base using (⟦_⟧; _,,_; [])
open import Cubical.Experiments.Relation.Operations using (tabulateᵣ; deriveᵣ; get; _|>_)
import Cubical.Experiments.Relation.Aggregation as Aggregation
import Cubical.HITs.CauchyReals.Example.Financial.Broker2.Pipeline.Implementation.Sources as Source

module QSum = Aggregation.Sum ℚ 0 ℚ._+_

module ValuationPipeline {clients trades instruments lots assets receipts stresses : ℕ}
  (sources : Source.Schema.DataSources clients trades instruments lots assets receipts stresses) where
  open Source.Schema clients trades instruments lots assets receipts stresses

  tradeRows : ⟦ Trades ⟧
  tradeRows = tabulateᵣ (λ id →
    let sourceRow = trade sources id in
    id ,, Trade.clientId sourceRow ,, Trade.instrumentId sourceRow ,, Trade.externalTradeId sourceRow ,,
    Trade.productCode sourceRow ,, Trade.settlementDate sourceRow ,, Trade.notional sourceRow ,, [])

  collateralRows : ⟦ Collateral ⟧
  collateralRows = tabulateᵣ (λ id →
    let sourceRow = collateralLot sources id in
    id ,, CollateralLot.clientId sourceRow ,, CollateralLot.assetId sourceRow ,,
    CollateralLot.custodyReference sourceRow ,, CollateralLot.units sourceRow ,, [])

  claimTotals collateralTotals : Valuation → ScenarioId → ClientId → ℚ
  claimTotals valuation scenario =
    tradeRows
      |> deriveᵣ "replacementClaim" (λ row →
          get "notional" row ℚ.· unitClaim valuation (get "instrumentId" row) scenario)
      |> QSum.groupSum (get "clientId") (get "replacementClaim")
  collateralTotals valuation scenario =
    collateralRows
      |> deriveᵣ "eligibleValue" (λ row →
          get "units" row ℚ.· eligibleUnitValue valuation (get "assetId" row) scenario)
      |> QSum.groupSum (get "clientId") (get "eligibleValue")

  -- Dense output includes every client key, including empty groups.
  clientRows : Valuation → ScenarioId → ⟦ ClientTotals ⟧
  clientRows valuation scenario = tabulateᵣ (λ client →
    client ,, clientReference sources client ,, scenario ,, snapshotId valuation ,,
    claimTotals valuation scenario client ,, collateralTotals valuation scenario client ,, [])
