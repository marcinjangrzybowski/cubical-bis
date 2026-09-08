{-# OPTIONS --safe --cubical #-}

-- Source contracts, identifiers and typed relational schemas. Source adapters
-- provide complete finite keyed catalogs; one index denotes one business row.
-- The model assumes the selected live trades, eligible custody lots and actual
-- cash receipts are complete and correctly attributed. External labels are
-- retained as metadata; stable typed internal keys drive all joins/grouping.
module Cubical.HITs.CauchyReals.Example.Financial.Broker2.Pipeline.Implementation.Sources where

open import Cubical.Data.Nat.Literals
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.FinData.Base using (Fin)
open import Cubical.Data.List.Base using (List)
open import Cubical.HITs.CauchyReals.Foundation.Rationals using (ℚ; module ℚ; fromNatℚ)
open import Cubical.Experiments.Relation.Base using (Fields; [_; _∶_,_; _∶_]; ⟦_⟧)
open import Agda.Builtin.String using (String)

module Schema (clients trades instruments lots assets receipts stresses : ℕ) where
  ClientId = Fin clients
  TradeId = Fin trades
  InstrumentId = Fin instruments
  LotId = Fin lots
  AssetId = Fin assets
  ReceiptId = Fin receipts
  ScenarioId = Fin (suc stresses)

  record Trade : Type₀ where
    field
      clientId : ClientId
      instrumentId : InstrumentId
      externalTradeId : String
      productCode : String
      settlementDate : ℕ
      notional : ℚ

  record CollateralLot : Type₀ where
    field
      clientId : ClientId
      assetId : AssetId
      custodyReference : String
      units : ℚ
      units-nonnegative : 0 ℚ.≤ units

  record CashReceipt : Type₀ where
    field
      clientId : ClientId
      externalReceiptId : String
      amount : ℚ
      amount-nonnegative : 0 ℚ.≤ amount

  record DataSources : Type₀ where
    field
      trade : TradeId → Trade
      collateralLot : LotId → CollateralLot
      cashReceipt : ReceiptId → CashReceipt
      clientReference : ClientId → String
      instrumentReference : InstrumentId → String
      assetReference : AssetId → String
  open DataSources public

  -- Values use one common account currency. unitClaim is a supplied signed
  -- replacement value per notional; eligibleUnitValue includes conversion,
  -- haircut and eligibility. Instrument pricing/custody are source contracts.
  -- Receipt cash is EXCLUDED from the collateral-lot catalog.
  record Valuation : Type₀ where
    field
      snapshotId : ℕ
      unitClaim : InstrumentId → ScenarioId → ℚ
      eligibleUnitValue : AssetId → ScenarioId → ℚ
      eligibleUnitValue-nonnegative : ∀ asset scenario → 0 ℚ.≤ eligibleUnitValue asset scenario
  open Valuation public

  Trades : Fields
  Trades = [ "tradeId" ∶ TradeId , "clientId" ∶ ClientId ,
    "instrumentId" ∶ InstrumentId , "externalTradeId" ∶ String ,
    "productCode" ∶ String , "settlementDate" ∶ ℕ , "notional" ∶ ℚ ]

  Collateral : Fields
  Collateral = [ "lotId" ∶ LotId , "clientId" ∶ ClientId , "assetId" ∶ AssetId ,
    "custodyReference" ∶ String , "units" ∶ ℚ ]

  ClientTotals : Fields
  ClientTotals = [ "clientId" ∶ ClientId , "externalClientId" ∶ String ,
    "scenarioId" ∶ ScenarioId , "snapshotId" ∶ ℕ ,
    "replacementClaim" ∶ ℚ , "eligibleCollateral" ∶ ℚ ]

  MarginCalls : Fields
  MarginCalls = [ "clientId" ∶ ClientId , "externalClientId" ∶ String ,
    "snapshotId" ∶ ℕ , "incrementalUpper" ∶ ℚ , "minimumTransfer" ∶ ℚ , "requestedCash" ∶ ℚ ]
