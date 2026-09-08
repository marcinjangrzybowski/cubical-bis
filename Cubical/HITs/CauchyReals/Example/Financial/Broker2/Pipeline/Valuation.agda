{-# OPTIONS --safe --cubical #-}

-- Relational valuation, grouping and its independent indexed specification.
-- Finite source catalogs materialize exactly one row per internal business ID.
module Cubical.HITs.CauchyReals.Example.Financial.Broker2.Pipeline.Valuation where

open import Cubical.HITs.CauchyReals.Example.Financial.Core.Finite
open import Cubical.HITs.CauchyReals.Foundation.Rationals using (ℚ; module ℚ)
open import Cubical.Data.FinData.Properties using (discreteFin)
open import Cubical.Relation.Nullary using (yes; no)
open import Cubical.Experiments.Relation.Base using (Fields; Row'; ⟦_⟧; _,,_; [])
open import Cubical.Experiments.Relation.Operations
open import Cubical.HITs.CauchyReals.Example.Financial.Broker2.Pipeline.FiniteRisk
import Cubical.HITs.CauchyReals.Example.Financial.Broker2.Pipeline.Sources as Source
import Cubical.HITs.CauchyReals.Example.Financial.Broker2.V03Stress as Model
import Cubical.HITs.CauchyReals.Example.Financial.Broker.Stage05Journal as Events

RowOf : Fields → Type₁
RowOf schema = Row' (Fields.fields schema)

module ValuationPipeline {clients trades instruments lots assets receipts stresses : ℕ}
  (sources : Source.Schema.DataSources clients trades instruments lots assets receipts stresses) where
  open Source.Schema clients trades instruments lots assets receipts stresses

  tradeRow : TradeId → RowOf Trades
  tradeRow id = id ,, Trade.clientId sourceRow ,, Trade.instrumentId sourceRow ,, Trade.externalTradeId sourceRow ,,
    Trade.productCode sourceRow ,, Trade.settlementDate sourceRow ,, Trade.notional sourceRow ,, []
    where sourceRow = trade sources id

  collateralRow : LotId → RowOf Collateral
  collateralRow id = id ,, CollateralLot.clientId sourceRow ,, CollateralLot.assetId sourceRow ,,
    CollateralLot.custodyReference sourceRow ,, CollateralLot.units sourceRow ,, []
    where sourceRow = collateralLot sources id

  tradeRows : ⟦ Trades ⟧
  tradeRows = tabulateᵣ tradeRow

  collateralRows : ⟦ Collateral ⟧
  collateralRows = tabulateᵣ collateralRow

  -- A total key lookup enriches each row once. The supplied valuation table
  -- is functional in instrument/asset and scenario: no join fan-out occurs.
  priceTrade : Valuation → ScenarioId → RowOf Trades → RowOf PricedTrades
  priceTrade valuation scenario (id ,, client ,, instrument ,, reference ,, product ,, date ,, quantity ,, []) =
    id ,, client ,, scenario ,, snapshotId valuation ,, (quantity ℚ.· unitClaim valuation instrument scenario) ,, []

  priceCollateral : Valuation → ScenarioId → RowOf Collateral → RowOf PricedCollateral
  priceCollateral valuation scenario (id ,, client ,, asset ,, reference ,, quantity ,, []) =
    id ,, client ,, scenario ,, snapshotId valuation ,, (quantity ℚ.· eligibleUnitValue valuation asset scenario) ,, []

  pricedTrades : Valuation → ScenarioId → ⟦ PricedTrades ⟧
  pricedTrades valuation scenario = projectᵣ (priceTrade valuation scenario) tradeRows

  pricedCollateral : Valuation → ScenarioId → ⟦ PricedCollateral ⟧
  pricedCollateral valuation scenario = projectᵣ (priceCollateral valuation scenario) collateralRows

  claimOwner : RowOf PricedTrades → ClientId
  claimOwner (_ ,, client ,, _ ,, _ ,, _ ,, []) = client

  claimValue : RowOf PricedTrades → ℚ
  claimValue (_ ,, _ ,, _ ,, _ ,, amount ,, []) = amount

  collateralOwner : RowOf PricedCollateral → ClientId
  collateralOwner (_ ,, client ,, _ ,, _ ,, _ ,, []) = client

  collateralValue : RowOf PricedCollateral → ℚ
  collateralValue (_ ,, _ ,, _ ,, _ ,, amount ,, []) = amount

  claimTotals collateralTotals : Valuation → ScenarioId → ClientId → ℚ
  claimTotals valuation scenario = QSum.groupSum claimOwner claimValue (pricedTrades valuation scenario)
  collateralTotals valuation scenario = QSum.groupSum collateralOwner collateralValue (pricedCollateral valuation scenario)

  -- The specification sums over business IDs directly, independently of the
  -- relation's row representation, projection and grouping operations.
  claimContribution : Valuation → ScenarioId → ClientId → TradeId → ℚ
  claimContribution valuation scenario client id with discreteFin (Trade.clientId (trade sources id)) client
  ... | yes _ = Trade.notional (trade sources id) ℚ.· unitClaim valuation (Trade.instrumentId (trade sources id)) scenario
  ... | no _ = 0

  collateralContribution : Valuation → ScenarioId → ClientId → LotId → ℚ
  collateralContribution valuation scenario client id with discreteFin (CollateralLot.clientId (collateralLot sources id)) client
  ... | yes _ = CollateralLot.units (collateralLot sources id)
    ℚ.· eligibleUnitValue valuation (CollateralLot.assetId (collateralLot sources id)) scenario
  ... | no _ = 0

  referenceClaims referenceCollateral : Valuation → ScenarioId → ClientId → ℚ
  referenceClaims valuation scenario client = QSum.finiteSum (claimContribution valuation scenario client)
  referenceCollateral valuation scenario client = QSum.finiteSum (collateralContribution valuation scenario client)

  private
    claim-row-correct : ∀ valuation scenario client id →
      QSum.atKey claimOwner claimValue client (priceTrade valuation scenario (tradeRow id))
        ≡ claimContribution valuation scenario client id
    claim-row-correct valuation scenario client id with discreteFin (Trade.clientId (trade sources id)) client
    ... | yes _ = refl
    ... | no _ = refl

    collateral-row-correct : ∀ valuation scenario client id →
      QSum.atKey collateralOwner collateralValue client (priceCollateral valuation scenario (collateralRow id))
        ≡ collateralContribution valuation scenario client id
    collateral-row-correct valuation scenario client id with discreteFin (CollateralLot.clientId (collateralLot sources id)) client
    ... | yes _ = refl
    ... | no _ = refl

  claims-refine-sum : ∀ valuation scenario client → claimTotals valuation scenario client ≡ referenceClaims valuation scenario client
  claims-refine-sum valuation scenario client =
    QSum.sum-project (priceTrade valuation scenario) (QSum.atKey claimOwner claimValue client) tradeRows
    ∙ QSum.sum-tabulate (λ row → QSum.atKey claimOwner claimValue client (priceTrade valuation scenario row)) tradeRow
    ∙ cong QSum.finiteSum (funExt (claim-row-correct valuation scenario client))

  collateral-refine-sum : ∀ valuation scenario client →
    collateralTotals valuation scenario client ≡ referenceCollateral valuation scenario client
  collateral-refine-sum valuation scenario client =
    QSum.sum-project (priceCollateral valuation scenario) (QSum.atKey collateralOwner collateralValue client) collateralRows
    ∙ QSum.sum-tabulate (λ row → QSum.atKey collateralOwner collateralValue client (priceCollateral valuation scenario row)) collateralRow
    ∙ cong QSum.finiteSum (funExt (collateral-row-correct valuation scenario client))

  collateralContribution-nonnegative : ∀ valuation scenario client id →
    0 ℚ.≤ collateralContribution valuation scenario client id
  collateralContribution-nonnegative valuation scenario client id
    with discreteFin (CollateralLot.clientId (collateralLot sources id)) client
  ... | yes _ = ≤ᵣ→≤ℚ 0 _ (isTrans≤≡ᵣ _ _ _
    (nonnegative-mul _ _
      (≤ℚ→≤ᵣ 0 _ (CollateralLot.units-nonnegative (collateralLot sources id)))
      (≤ℚ→≤ᵣ 0 _ (eligibleUnitValue-nonnegative valuation (CollateralLot.assetId (collateralLot sources id)) scenario)))
    (·ᵣ-rat _ _))
  ... | no _ = ℚ.isRefl≤ 0

  referenceCollateral-nonnegative : ∀ valuation scenario client → 0 ℚ.≤ referenceCollateral valuation scenario client
  referenceCollateral-nonnegative valuation scenario client = finiteSum-nonnegative _
    (collateralContribution-nonnegative valuation scenario client)

  collateralTotals-nonnegative : ∀ valuation scenario client → 0 ℚ.≤ collateralTotals valuation scenario client
  collateralTotals-nonnegative valuation scenario client = subst (λ q → 0 ℚ.≤ q)
    (sym (collateral-refine-sum valuation scenario client)) (referenceCollateral-nonnegative valuation scenario client)

  pipelineMarket referenceMarket : Valuation → Model.Market clients stresses
  pipelineMarket valuation = Model.market-data
    (λ scenario client → rat (claimTotals valuation scenario client))
    (λ scenario client → rat (collateralTotals valuation scenario client))
    (λ scenario client → ≤ℚ→≤ᵣ 0 _ (collateralTotals-nonnegative valuation scenario client))
  referenceMarket valuation = Model.market-data
    (λ scenario client → rat (referenceClaims valuation scenario client))
    (λ scenario client → rat (referenceCollateral valuation scenario client))
    (λ scenario client → ≤ℚ→≤ᵣ 0 _ (referenceCollateral-nonnegative valuation scenario client))

  -- Equality includes the model's proof-bearing collateral fields.
  market-refines-model : ∀ valuation → pipelineMarket valuation ≡ referenceMarket valuation
  market-refines-model valuation i .Model.claims scenario client = cong rat (claims-refine-sum valuation scenario client) i
  market-refines-model valuation i .Model.collateral scenario client = cong rat (collateral-refine-sum valuation scenario client) i
  market-refines-model valuation i .Model.collateral-nonnegative scenario client =
    isProp→PathP (λ j → isProp≤ᵣ 0 (cong rat (collateral-refine-sum valuation scenario client) j))
      (Model.collateral-nonnegative (pipelineMarket valuation) scenario client)
      (Model.collateral-nonnegative (referenceMarket valuation) scenario client) i

  -- Dense output: even a client with no trade rows receives a keyed result.
  clientRows : Valuation → ScenarioId → ⟦ ClientTotals ⟧
  clientRows valuation scenario = tabulateᵣ (λ client → client ,, clientReference sources client ,,
    scenario ,, snapshotId valuation ,, claimTotals valuation scenario client ,, collateralTotals valuation scenario client ,, [])

  referenceClientRows : Valuation → ScenarioId → ⟦ ClientTotals ⟧
  referenceClientRows valuation scenario = tabulateᵣ (λ client → client ,, clientReference sources client ,,
    scenario ,, snapshotId valuation ,, referenceClaims valuation scenario client ,, referenceCollateral valuation scenario client ,, [])

  clientRows-refine : ∀ valuation scenario → clientRows valuation scenario ≡ referenceClientRows valuation scenario
  clientRows-refine valuation scenario = tabulate-cong _ _ (λ client →
    cong₂ (λ claim collateral → client ,, clientReference sources client ,, scenario ,, snapshotId valuation ,, claim ,, collateral ,, [])
      (claims-refine-sum valuation scenario client) (collateral-refine-sum valuation scenario client))

  receiptCatalog : Events.EventCatalog receipts clients
  receiptCatalog = Events.event-catalog
    (λ receipt → CashReceipt.clientId (cashReceipt sources receipt))
    (λ receipt → CashReceipt.amount (cashReceipt sources receipt))
    (λ receipt → CashReceipt.amount-nonnegative (cashReceipt sources receipt))
