{-# OPTIONS --safe --cubical #-}

-- Properties of the separate executable relational pipeline.
-- All returned amounts, rows, states and status tags come from Implementation.
-- This module supplies assumptions, model projections and safety certificates.
module Cubical.HITs.CauchyReals.Example.Financial.Broker2.Pipeline.Properties.Correctness where

open import Cubical.HITs.CauchyReals.Example.Financial.Core.Finite
open import Cubical.HITs.CauchyReals.Foundation.Rationals using (ℚ; module ℚ)
open import Cubical.Experiments.Relation.Base using (⟦_⟧; _,,_; [])
open import Cubical.Experiments.Relation.Operations
open import Cubical.Data.FinData.Properties using (∀Dec)
open import Cubical.Data.Sum.Base using (inl; inr)
open import Cubical.Relation.Nullary using (¬_; yes; no)
open import Cubical.HITs.CauchyReals.Example.Financial.Broker2.Pipeline.Properties.FiniteRisk
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
import Cubical.HITs.CauchyReals.Example.Financial.Broker2.Pipeline.Implementation.Margin as Implementation
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.Shortfall
import Cubical.HITs.CauchyReals.Example.Financial.Risk.WorstCase as Worst
import Cubical.HITs.CauchyReals.Example.Financial.Broker2.Pipeline.Implementation.Sources as Source
import Cubical.HITs.CauchyReals.Example.Financial.Broker2.Pipeline.Properties.Valuation as Pricing
import Cubical.HITs.CauchyReals.Example.Financial.Broker2.Pipeline.Properties.Receipts as Receipts
import Cubical.HITs.CauchyReals.Example.Financial.Broker2.V07Revaluation as Model
import Cubical.HITs.CauchyReals.Example.Financial.Broker2.V05Tolerance as Tolerance
import Cubical.HITs.CauchyReals.Example.Financial.Broker2.V04Rational as Rational
import Cubical.HITs.CauchyReals.Example.Financial.Broker2.V03Stress as Stress
import Cubical.HITs.CauchyReals.Example.Financial.Broker.Stage07Calls as Transfers

private
  swap-add : ∀ x y z → (x +ᵣ y) +ᵣ z ≡ (x +ᵣ z) +ᵣ y
  swap-add x y z = ℝ!

module Pipeline {clients trades instruments lots assets receipts stresses : ℕ}
  (sources : Source.Schema.DataSources clients trades instruments lots assets receipts stresses) where
  open Source.Schema clients trades instruments lots assets receipts stresses
  module Values = Pricing.ValuationPipeline sources
  module Cash = Receipts.RelationalReceipts Values.receiptCatalog
    (λ receipt → CashReceipt.externalReceiptId (cashReceipt sources receipt))
  module Abstract = Model.Engine {stresses = stresses} Values.receiptCatalog

  module Code = Implementation.Pipeline sources
  open Code using (State; state; valuation; ledger; claimReserve; collateralReserve; reserve; receive) public

  decode referenceState : State → Abstract.State
  decode s = Abstract.engine-state (Values.pipelineMarket (valuation s)) (ledger s)
  referenceState s = Abstract.engine-state (Values.referenceMarket (valuation s)) (ledger s)

  decode-refines-reference : ∀ s → decode s ≡ referenceState s
  decode-refines-reference s = Abstract.Old.state-path _ _ (Values.market-refines-model (valuation s)) refl

  Report : State → Type₀
  Report s = Abstract.Report (decode s)

  -- These are computed from relationally valued/grouped trades, custody lots
  -- and the selected/grouped receipt catalog, rather than an assumed margin.
  module Initial (s : State) = Rational.RationalInputs
    (Values.claimTotals (valuation s)) (Values.collateralTotals (valuation s))
    (Values.collateralTotals-nonnegative (valuation s))
    (Cash.balances (ledger s)) (Cash.balances-nonnegative (ledger s))

  initial-book-refines : ∀ s → Initial.initialState s ≡ Abstract.view (decode s)
  initial-book-refines s = Stress.state-path _ _ refl
    (funExt (λ client → cong rat (Cash.balances-refine-paid (ledger s) client)))

  initial-quote-exact : ∀ s client → Stress.quoteCall (Abstract.view (decode s)) client
    ≡ rat (Code.initialAmounts s client)
  initial-quote-exact s client = cong (λ b → Stress.quoteCall b client) (sym (initial-book-refines s))
    ∙ cong Worst.worstCase (funExt (λ scenario →
        cong (stopLoss (rat (Values.claimTotals (valuation s) scenario client)))
          (+ᵣ-rat (Values.collateralTotals (valuation s) scenario client) (Cash.balances (ledger s) client))
        ∙ stopLoss-rat (Values.claimTotals (valuation s) scenario client)
          (Values.collateralTotals (valuation s) scenario client ℚ.+ Cash.balances (ledger s) client)))
    ∙ maxFold-exact (λ scenario → Initial.scenarioGap s scenario client)
        (λ scenario → ℚ.≤max' (Values.claimTotals (valuation s) scenario client ℚ.-
          (Values.collateralTotals (valuation s) scenario client ℚ.+ Cash.balances (ledger s) client)) 0)

  initialReport : ∀ s → Report s
  initialReport s .Rational.amounts = Code.initialAmounts s
  initialReport s .Rational.amounts-nonnegative client = ≤ᵣ→≤ℚ 0 _
    (isTrans≤≡ᵣ _ _ _ (Stress.quote-nonnegative (Abstract.view (decode s)) client) (initial-quote-exact s client))
  initialReport s .Rational.dominates client = ≡ᵣWeaken≤ᵣ _ _ (initial-quote-exact s client)

  initialReport-exact : ∀ s → Rational.Exact (initialReport s)
  initialReport-exact = initial-quote-exact

  -- Summing positive scenario changes is conservative and fully computed;
  -- it is not claimed to be a minimal reserve or a calibrated IM measure.
  certifiedUpdate : ∀ s next → Abstract.Update (decode s)
  certifiedUpdate s next .Abstract.nextMarket = Values.pipelineMarket next
  certifiedUpdate s next .Abstract.drift .Abstract.Changes.claimShock client = rat (claimReserve s next client)
  certifiedUpdate s next .Abstract.drift .Abstract.Changes.collateralDrop client = rat (collateralReserve s next client)
  certifiedUpdate s next .Abstract.drift .Abstract.Changes.claimShock-nonnegative client = ≤ℚ→≤ᵣ 0 _
    (differenceReserve-nonnegative
      (λ scenario → Values.claimTotals (valuation s) scenario client)
      (λ scenario → Values.claimTotals next scenario client))
  certifiedUpdate s next .Abstract.drift .Abstract.Changes.collateralDrop-nonnegative client = ≤ℚ→≤ᵣ 0 _
    (differenceReserve-nonnegative
      (λ scenario → Values.collateralTotals next scenario client)
      (λ scenario → Values.collateralTotals (valuation s) scenario client))
  certifiedUpdate s next .Abstract.drift .Abstract.Changes.claim-rise scenario member client =
    differenceReserve-covers
      (λ ω → Values.claimTotals (valuation s) ω client) (λ ω → Values.claimTotals next ω client) scenario
  certifiedUpdate s next .Abstract.drift .Abstract.Changes.collateral-fall scenario member client =
    isTrans≤≡ᵣ _ _ _
      (≤ᵣ-+o _ _ cash (differenceReserve-covers
        (λ ω → Values.collateralTotals next ω client) (λ ω → Values.collateralTotals (valuation s) ω client) scenario))
      reorder
    where
    cash = rat (Cash.Journal.paid (ledger s) client)
    reorder : (rat (Values.collateralTotals next scenario client) +ᵣ rat (collateralReserve s next client)) +ᵣ cash
      ≡ (rat (Values.collateralTotals next scenario client) +ᵣ cash) +ᵣ rat (collateralReserve s next client)
    reorder = swap-add _ _ cash
  certifiedUpdate s next .Abstract.reserve = reserve s next
  certifiedUpdate s next .Abstract.reserve-nonnegative client = ≤ᵣ→≤ℚ 0 _
    (isTrans≤≡ᵣ _ _ _
      (nonnegative-add _ _
        (Abstract.Changes.claimShock-nonnegative (Abstract.drift (certifiedUpdate s next)) client)
        (Abstract.Changes.collateralDrop-nonnegative (Abstract.drift (certifiedUpdate s next)) client))
      (+ᵣ-rat (claimReserve s next client) (collateralReserve s next client)))
  certifiedUpdate s next .Abstract.reserve-bound client = ≡ᵣWeaken≤ᵣ _ _
    (+ᵣ-rat (claimReserve s next client) (collateralReserve s next client))

  transfer-refines-model : ∀ gap mta → Implementation.transferAmount gap mta ≡ Transfers.transferAmount gap mta
  transfer-refines-model gap mta with ℚ.≤Dec gap mta
  ... | yes _ = refl
  ... | no _ = refl

  quote-refines-model : ∀ s report next mta → Code.quoteCall s (Rational.amounts report) next mta ≡
    Abstract.quoteCall (decode s) report (certifiedUpdate s next) mta
  quote-refines-model s report next mta = funExt (λ client →
    transfer-refines-model (Code.upperAfterRevaluation s (Rational.amounts report) next client) (mta client))

  receive-refines-model : ∀ s next deliveries → decode (receive s next deliveries) ≡
    Abstract.receive (decode s) (certifiedUpdate s next) (Cash.decodeBatch deliveries)
  receive-refines-model s next deliveries = Abstract.Old.state-path _ _ refl
    (Cash.receiveLedger-refines-journal (ledger s) deliveries)

  Adequate : ∀ s → Report s → Valuation → Rational.Payments clients → Cash.Deliveries → Type₀
  Adequate s report next mta deliveries = ∀ client →
    Code.quoteCall s (Rational.amounts report) next mta client ℚ.≤ Cash.deltaBalances (ledger s) deliveries client

  -- Equality of the operational gate and the model gate, in both directions.
  -- Only newly selected receipts enter the right-hand side of this comparison.
  adequacy-refines-model : ∀ s report next mta deliveries →
    Adequate s report next mta deliveries ≡
    Abstract.Adequate (decode s) report (certifiedUpdate s next) mta (Cash.decodeBatch deliveries)
  adequacy-refines-model s report next mta deliveries i = ∀ client →
    funExt⁻ (quote-refines-model s report next mta) client i ℚ.≤
      Cash.deltaBalances-refine-newlyPaid (ledger s) deliveries client i

  receive-correct : ∀ s report next mta → Rational.Nonnegative mta → ∀ deliveries →
    Adequate s report next mta deliveries → Abstract.Guarantee (decode (receive s next deliveries)) mta
  receive-correct s report next mta mta₊ deliveries enough =
    subst (λ t → Abstract.Guarantee t mta) (sym (receive-refines-model s next deliveries))
      (Abstract.receive-correct (decode s) report (certifiedUpdate s next) mta mta₊
        (Cash.decodeBatch deliveries)
        (subst (λ P → P) (adequacy-refines-model s report next mta deliveries) enough))

  -- The public economic guarantee refers to independent indexed source sums,
  -- so correctness is not merely a theorem about the output of GROUP BY.
  Guarantee : State → Rational.Payments clients → Type₀
  Guarantee s mta = Abstract.Guarantee (referenceState s) mta

  reference-guarantee : ∀ s report next mta → Rational.Nonnegative mta → ∀ deliveries →
    Adequate s report next mta deliveries → Guarantee (receive s next deliveries) mta
  reference-guarantee s report next mta mta₊ deliveries enough =
    subst (λ t → Abstract.Guarantee t mta) (decode-refines-reference (receive s next deliveries))
      (receive-correct s report next mta mta₊ deliveries enough)

  zero-mta-safe : ∀ s report next deliveries → Adequate s report next Tolerance.zeroMTA deliveries →
    Stress.Safe (Abstract.view (referenceState (receive s next deliveries)))
  zero-mta-safe s report next deliveries enough =
    subst (λ t → Stress.Safe (Abstract.view t))
      (sym (receive-refines-model s next deliveries) ∙ decode-refines-reference (receive s next deliveries))
      (Abstract.zero-mta-safe (decode s) report (certifiedUpdate s next) (Cash.decodeBatch deliveries)
        (subst (λ P → P) (adequacy-refines-model s report next Tolerance.zeroMTA deliveries) enough))

  zero-mta-loss-zero : ∀ s report next deliveries → Adequate s report next Tolerance.zeroMTA deliveries →
    ∀ scenario θ → Stress.loss (Abstract.view (referenceState (receive s next deliveries))) scenario θ ≡ 0
  zero-mta-loss-zero s report next deliveries enough = Stress.safe-loss-zero
    (Abstract.view (referenceState (receive s next deliveries)))
    (zero-mta-safe s report next deliveries enough)

  -- Even an insufficient receipt leaves a certified report for the next cycle.
  -- This calculation subtracts the relational DELTA, never the closing balance.
  modelNextReport : ∀ s → Report s → ∀ next deliveries →
    Abstract.Report (Abstract.receive (decode s) (certifiedUpdate s next) (Cash.decodeBatch deliveries))
  modelNextReport s report next deliveries =
    Abstract.Old.advanceReport (Abstract.revalue (decode s) (Values.pipelineMarket next))
      (Abstract.refreshReport (decode s) report (certifiedUpdate s next)) (Cash.decodeBatch deliveries)

  nextAmounts-refine : ∀ s report next deliveries client → Code.advanceAmounts s (Rational.amounts report) next deliveries client ≡
    Rational.amounts (modelNextReport s report next deliveries) client
  nextAmounts-refine s report next deliveries client =
    cong (λ paid → ℚ.max (Code.upperAfterRevaluation s (Rational.amounts report) next client ℚ.- paid) 0)
      (Cash.deltaBalances-refine-newlyPaid (ledger s) deliveries client)

  advanceReport : ∀ s → Report s → ∀ next deliveries → Report (receive s next deliveries)
  advanceReport s report next deliveries .Rational.amounts = Code.advanceAmounts s (Rational.amounts report) next deliveries
  advanceReport s report next deliveries .Rational.amounts-nonnegative client =
    ℚ.≤max' (Code.upperAfterRevaluation s (Rational.amounts report) next client ℚ.- Cash.deltaBalances (ledger s) deliveries client) 0
  advanceReport s report next deliveries .Rational.dominates client =
    subst2 (λ t amount → Stress.quoteCall (Abstract.view t) client ≤ᵣ rat amount)
      (sym (receive-refines-model s next deliveries)) (sym (nextAmounts-refine s report next deliveries client))
      (Rational.dominates (modelNextReport s report next deliveries) client)

  -- Evidence is indexed by the tag returned by the ordinary data program.
  data Assessment (s : State) (report : Report s) (next : Valuation)
    (mta : Rational.Payments clients) (deliveries : Cash.Deliveries) : Code.Status → Type₀ where
    controlled : Adequate s report next mta deliveries → Guarantee (receive s next deliveries) mta →
      Assessment s report next mta deliveries Code.controlled
    unmet-quote : (client : ClientId) →
      ¬ (Code.quoteCall s (Rational.amounts report) next mta client ℚ.≤ Cash.deltaBalances (ledger s) deliveries client) →
      Assessment s report next mta deliveries (Code.unmet-quote client)

  assess-correct : ∀ s report next mta → Rational.Nonnegative mta → ∀ deliveries →
    Assessment s report next mta deliveries (Code.assess s (Rational.amounts report) next mta deliveries)
  assess-correct s report next mta mta₊ deliveries with ∀Dec
    (λ client → Code.quoteCall s (Rational.amounts report) next mta client ℚ.≤ Cash.deltaBalances (ledger s) deliveries client)
    (λ client → ℚ.≤Dec (Code.quoteCall s (Rational.amounts report) next mta client) (Cash.deltaBalances (ledger s) deliveries client))
  ... | inl enough = controlled enough (reference-guarantee s report next mta mta₊ deliveries enough)
  ... | inr (client , insufficient) = unmet-quote client insufficient

  -- No second implementation of process lives here. These fields describe
  -- exactly the data returned by Code.process, including its status tag.
  record CertifiedOutput (s : State) (report : Report s) (next : Valuation)
    (mta : Rational.Payments clients) (deliveries : Cash.Deliveries) : Type₀ where
    private
      result = Code.process s (Rational.amounts report) next mta deliveries
    field
      remaining-nonnegative : Rational.Nonnegative (Code.next-amounts result)
      remaining-valid : ∀ client →
        Stress.quoteCall (Abstract.view (decode (Code.next-state result))) client ≤ᵣ rat (Code.next-amounts result client)
      status-correct : Assessment s report next mta deliveries (Code.status result)
  open CertifiedOutput public

  certify : ∀ s report next mta → Rational.Nonnegative mta → ∀ deliveries →
    CertifiedOutput s report next mta deliveries
  certify s report next mta mta₊ deliveries .remaining-nonnegative =
    Rational.amounts-nonnegative (advanceReport s report next deliveries)
  certify s report next mta mta₊ deliveries .remaining-valid =
    Rational.dominates (advanceReport s report next deliveries)
  certify s report next mta mta₊ deliveries .status-correct = assess-correct s report next mta mta₊ deliveries
