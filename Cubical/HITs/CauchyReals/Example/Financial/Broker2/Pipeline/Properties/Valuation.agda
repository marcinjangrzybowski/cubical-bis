{-# OPTIONS --safe --cubical #-}

-- Properties and model adapters for the runtime valuation pipeline.
-- The indexed specification is independent of relation row operations.
module Cubical.HITs.CauchyReals.Example.Financial.Broker2.Pipeline.Properties.Valuation where

open import Cubical.HITs.CauchyReals.Example.Financial.Core.Finite
open import Cubical.HITs.CauchyReals.Foundation.Rationals using (ℚ; module ℚ)
open import Cubical.Data.FinData.Properties using (discreteFin)
open import Cubical.Relation.Nullary using (yes; no)
open import Cubical.Experiments.Relation.Base using (Fields; Row'; ⟦_⟧; _,,_; []; insert)
open import Cubical.Experiments.Relation.Operations
open import Cubical.HITs.CauchyReals.Example.Financial.Broker2.Pipeline.Properties.FiniteRisk
import Cubical.HITs.CauchyReals.Example.Financial.Broker2.Pipeline.Implementation.Sources as Source
import Cubical.HITs.CauchyReals.Example.Financial.Broker2.Pipeline.Implementation.Valuation as Implementation
import Cubical.HITs.CauchyReals.Example.Financial.Broker2.V03Stress as Model
import Cubical.HITs.CauchyReals.Example.Financial.Broker.Stage05Journal as Events

RowOf : Fields → Type₁
RowOf schema = Row' (Fields.fields schema)

module ValuationPipeline {clients trades instruments lots assets receipts stresses : ℕ}
  (sources : Source.Schema.DataSources clients trades instruments lots assets receipts stresses) where
  open Source.Schema clients trades instruments lots assets receipts stresses
  open Implementation.ValuationPipeline sources public

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
    -- Source adapters are named only inside these proofs of tabulation.
    tradeRow : TradeId → RowOf Trades
    tradeRow id = id ,, Trade.clientId sourceRow ,, Trade.instrumentId sourceRow ,, Trade.externalTradeId sourceRow ,,
      Trade.productCode sourceRow ,, Trade.settlementDate sourceRow ,, Trade.notional sourceRow ,, []
      where sourceRow = trade sources id

    collateralRow : LotId → RowOf Collateral
    collateralRow id = id ,, CollateralLot.clientId sourceRow ,, CollateralLot.assetId sourceRow ,,
      CollateralLot.custodyReference sourceRow ,, CollateralLot.units sourceRow ,, []
      where sourceRow = collateralLot sources id

    claim-row-correct : ∀ valuation scenario client id →
      QSum.atKey (get "clientId") (get "replacementClaim") client
        (insert "replacementClaim"
          (get "notional" (tradeRow id) ℚ.· unitClaim valuation (get "instrumentId" (tradeRow id)) scenario)
          (tradeRow id))
        ≡ claimContribution valuation scenario client id
    claim-row-correct valuation scenario client id with discreteFin (Trade.clientId (trade sources id)) client
    ... | yes _ = refl
    ... | no _ = refl

    collateral-row-correct : ∀ valuation scenario client id →
      QSum.atKey (get "clientId") (get "eligibleValue") client
        (insert "eligibleValue"
          (get "units" (collateralRow id) ℚ.· eligibleUnitValue valuation (get "assetId" (collateralRow id)) scenario)
          (collateralRow id))
        ≡ collateralContribution valuation scenario client id
    collateral-row-correct valuation scenario client id with discreteFin (CollateralLot.clientId (collateralLot sources id)) client
    ... | yes _ = refl
    ... | no _ = refl

  claims-refine-sum : ∀ valuation scenario client → claimTotals valuation scenario client ≡ referenceClaims valuation scenario client
  claims-refine-sum valuation scenario client =
    QSum.sum-derive "replacementClaim"
      (λ row → get "notional" row ℚ.· unitClaim valuation (get "instrumentId" row) scenario)
      (QSum.atKey (get "clientId") (get "replacementClaim") client) tradeRows
    ∙ QSum.sum-tabulate (λ row → QSum.atKey (get "clientId") (get "replacementClaim") client
        (insert "replacementClaim"
          (get "notional" row ℚ.· unitClaim valuation (get "instrumentId" row) scenario) row)) tradeRow
    ∙ cong QSum.finiteSum (funExt (claim-row-correct valuation scenario client))

  collateral-refine-sum : ∀ valuation scenario client →
    collateralTotals valuation scenario client ≡ referenceCollateral valuation scenario client
  collateral-refine-sum valuation scenario client =
    QSum.sum-derive "eligibleValue"
      (λ row → get "units" row ℚ.· eligibleUnitValue valuation (get "assetId" row) scenario)
      (QSum.atKey (get "clientId") (get "eligibleValue") client) collateralRows
    ∙ QSum.sum-tabulate (λ row → QSum.atKey (get "clientId") (get "eligibleValue") client
        (insert "eligibleValue"
          (get "units" row ℚ.· eligibleUnitValue valuation (get "assetId" row) scenario) row)) collateralRow
    ∙ cong QSum.finiteSum (funExt (collateral-row-correct valuation scenario client))

  collateralContribution-nonnegative : ∀ valuation scenario client id →
    0 ℚ.≤ collateralContribution valuation scenario client id
  collateralContribution-nonnegative valuation scenario client id
    with discreteFin (CollateralLot.clientId (collateralLot sources id)) client
  ... | yes _ = ≤ᵣ→≤ℚ 0 _ (isTrans≤≡ᵣ _ _ _
    (nonnegative-mul _ _
      (≤ℚ→≤ᵣ 0 _ (CollateralLot.units-nonnegative (collateralLot sources id)))
      (≤ℚ→≤ᵣ 0 _ (eligibleUnitValue-nonnegative valuation (CollateralLot.assetId (collateralLot sources id)) scenario)))
    (sym (rat·ᵣrat _ _)))
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

  private
    -- This local annotation fixes the output schema in the congruence proof.
    clientResult : Valuation → ScenarioId → ClientId → ℚ → ℚ → RowOf ClientTotals
    clientResult valuation scenario client claim collateral = client ,, clientReference sources client ,,
      scenario ,, snapshotId valuation ,, claim ,, collateral ,, []

  referenceClientRows : Valuation → ScenarioId → ⟦ ClientTotals ⟧
  referenceClientRows valuation scenario = tabulateᵣ (λ client → clientResult valuation scenario client
    (referenceClaims valuation scenario client) (referenceCollateral valuation scenario client))

  clientRows-refine : ∀ valuation scenario → clientRows valuation scenario ≡ referenceClientRows valuation scenario
  clientRows-refine valuation scenario = tabulate-cong _ _ (λ client →
    cong₂ (clientResult valuation scenario client)
      (claims-refine-sum valuation scenario client) (collateral-refine-sum valuation scenario client))

  receiptCatalog : Events.EventCatalog receipts clients
  receiptCatalog = Events.event-catalog
    (λ receipt → CashReceipt.clientId (cashReceipt sources receipt))
    (λ receipt → CashReceipt.amount (cashReceipt sources receipt))
    (λ receipt → CashReceipt.amount-nonnegative (cashReceipt sources receipt))
