{-# OPTIONS --safe --cubical #-}

-- Executable data pipeline. There are no margin-model imports, safety
-- certificates or refinement proofs here: reports are ordinary rational data.
module Cubical.HITs.CauchyReals.Example.Financial.Broker2.Pipeline.Implementation.Margin where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Literals
open import Cubical.Data.FinData.Properties using (∀Dec)
open import Cubical.Data.Sum.Base using (inl; inr)
open import Cubical.Relation.Nullary using (yes; no)
open import Cubical.HITs.CauchyReals.Foundation.Rationals using (ℚ; module ℚ; fromNatℚ)
open import Cubical.Experiments.Relation.Base using (⟦_⟧; _,,_; [])
open import Cubical.Experiments.Relation.Operations
import Cubical.Experiments.Relation.Aggregation as Aggregation
import Cubical.HITs.CauchyReals.Example.Financial.Broker2.Pipeline.Implementation.Sources as Source
import Cubical.HITs.CauchyReals.Example.Financial.Broker2.Pipeline.Implementation.Valuation as ValuationData
import Cubical.HITs.CauchyReals.Example.Financial.Broker2.Pipeline.Implementation.Receipts as ReceiptData

module QSum = Aggregation.Sum ℚ 0 ℚ._+_
module QMax = Aggregation.Sum ℚ 0 ℚ.max

-- The business rule requests the whole gap only when it exceeds the MTA.
transferAmount : ℚ → ℚ → ℚ
transferAmount gap mta with ℚ.≤Dec gap mta
... | yes _ = 0
... | no _ = gap

module Pipeline {clients trades instruments lots assets receipts stresses : ℕ}
  (sources : Source.Schema.DataSources clients trades instruments lots assets receipts stresses) where
  open Source.Schema clients trades instruments lots assets receipts stresses
  module Values = ValuationData.ValuationPipeline sources
  module Cash = ReceiptData.RelationalReceipts
    (λ id → CashReceipt.clientId (cashReceipt sources id))
    (λ id → CashReceipt.amount (cashReceipt sources id))
    (λ id → CashReceipt.externalReceiptId (cashReceipt sources id))

  Amounts : Type₀
  Amounts = ClientId → ℚ

  record State : Type₀ where
    constructor state
    field
      valuation : Valuation
      ledger : Cash.Ledger
  open State public

  initialAmounts : State → Amounts
  initialAmounts s client = QMax.finiteSum (λ scenario →
    ℚ.max (Values.claimTotals (valuation s) scenario client ℚ.-
      (Values.collateralTotals (valuation s) scenario client ℚ.+ Cash.balances (ledger s) client)) 0)

  claimReserve collateralReserve : State → Valuation → Amounts
  claimReserve s next client = QSum.finiteSum (λ scenario → ℚ.max
    (Values.claimTotals next scenario client ℚ.- Values.claimTotals (valuation s) scenario client) 0)
  collateralReserve s next client = QSum.finiteSum (λ scenario → ℚ.max
    (Values.collateralTotals (valuation s) scenario client ℚ.- Values.collateralTotals next scenario client) 0)

  reserve : State → Valuation → Amounts
  reserve s next client = claimReserve s next client ℚ.+ collateralReserve s next client

  upperAfterRevaluation : State → Amounts → Valuation → Amounts
  upperAfterRevaluation s upper next client = upper client ℚ.+ reserve s next client

  quoteCall : State → Amounts → Valuation → Amounts → Amounts
  quoteCall s upper next mta client = transferAmount (upperAfterRevaluation s upper next client) (mta client)

  callRows : State → Amounts → Valuation → Amounts → ⟦ MarginCalls ⟧
  callRows s upper next mta = tabulateᵣ (λ client →
    client ,, clientReference sources client ,, snapshotId next ,,
    upperAfterRevaluation s upper next client ,, mta client ,, quoteCall s upper next mta client ,, [])

  receive : State → Valuation → Cash.Deliveries → State
  receive s next deliveries = state next (Cash.receiveLedger (ledger s) deliveries)

  advanceAmounts : State → Amounts → Valuation → Cash.Deliveries → Amounts
  advanceAmounts s upper next deliveries client =
    ℚ.max (upperAfterRevaluation s upper next client ℚ.- Cash.deltaBalances (ledger s) deliveries client) 0

  data Status : Type₀ where
    controlled : Status
    unmet-quote : ClientId → Status

  assess : State → Amounts → Valuation → Amounts → Cash.Deliveries → Status
  assess s upper next mta deliveries with ∀Dec
    (λ client → quoteCall s upper next mta client ℚ.≤ Cash.deltaBalances (ledger s) deliveries client)
    (λ client → ℚ.≤Dec (quoteCall s upper next mta client) (Cash.deltaBalances (ledger s) deliveries client))
  ... | inl _ = controlled
  ... | inr (client , _) = unmet-quote client

  record Output : Type₁ where
    constructor output
    field
      next-state : State
      next-amounts : Amounts
      calls : ⟦ MarginCalls ⟧
      status : Status
  open Output public

  -- Calls are the pre-receipt requests assessed for this batch. The remaining
  -- incremental amounts are returned separately, including after partial pay.
  process : State → Amounts → Valuation → Amounts → Cash.Deliveries → Output
  process s upper next mta deliveries = output
    (receive s next deliveries) (advanceAmounts s upper next deliveries)
    (callRows s upper next mta) (assess s upper next mta deliveries)
