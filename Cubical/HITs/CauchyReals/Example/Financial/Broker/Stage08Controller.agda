{-# OPTIONS --safe --cubical #-}

-- End-to-end margin control: conservative requirements, revaluation,
-- minimum transfers, inventory-backed collateral, and identified receipts.
-- The external catalog represents actual additional cash receipts. It must
-- not include cash already present in the collateral allocation; distinct
-- IDs must denote distinct receipts. Authentication/custody are not modeled.
module Cubical.HITs.CauchyReals.Example.Financial.Broker.Stage08Controller where

open import Cubical.HITs.CauchyReals.Example.Financial.Core.Finite
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.Shortfall
open import Cubical.HITs.CauchyReals.Foundation.Rationals using (ℚ; module ℚ)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Data.FinData.Properties using (∀Dec)
open import Cubical.Data.Sum.Base using (inl; inr)
open import Cubical.Data.Sigma.Properties using (Σ≡Prop)
import Cubical.HITs.CauchyReals.Example.Financial.Margin.CounterpartyRisk as Credit
import Cubical.HITs.CauchyReals.Example.Financial.Broker.Stage03NettingSets as Netting
import Cubical.HITs.CauchyReals.Example.Financial.Broker.Stage04Collateral as Collateral
import Cubical.HITs.CauchyReals.Example.Financial.Broker.Stage05Journal as Receipts
import Cubical.HITs.CauchyReals.Example.Financial.Broker.Stage06Revaluation as Repricing
import Cubical.HITs.CauchyReals.Example.Financial.Broker.Stage07Calls as Transfers

module Controller {clients assets events : ℕ} {State : Type₀}
  (Allowed : State → Type₀)
  (allocation : Collateral.CollateralAllocation clients assets)
  (oldValuation newValuation : Collateral.CollateralValuation State clients assets)
  (oldClaims newClaims : State → Vector clients)
  (catalog : Receipts.EventCatalog events clients) where

  oldCollateral newCollateral : State → Vector clients
  oldCollateral = Collateral.eligibleValue allocation oldValuation
  newCollateral = Collateral.eligibleValue allocation newValuation

  module Old = Netting.NettingSets Allowed oldClaims oldCollateral
  module New = Netting.NettingSets Allowed newClaims newCollateral
  module Changes = Repricing.Revaluation {clients = clients} Allowed
  module Journal = Receipts.Journal catalog

  -- A rational upper reserve is a supplied certificate of a real bound.
  -- We neither round an arbitrary real by comparison nor claim leastness.
  module Policy (reports : Old.Reports)
    (drift : Changes.DriftBounds oldClaims oldCollateral newClaims newCollateral)
    (reserve : Fin clients → ℚ)
    (reserve-nonnegative : ∀ client → 0 ℚ.≤ reserve client)
    (reserve-bound : ∀ client → Changes.driftReserve drift client ≤ᵣ rat (reserve client)) where

    requirements : Fin clients → ℚ
    requirements client = Old.upperCalls reports client ℚ.+ reserve client

    requirements-nonnegative : ∀ client → 0 ℚ.≤ requirements client
    requirements-nonnegative client = ≤ᵣ→≤ℚ 0 (requirements client)
      (isTrans≤≡ᵣ _ _ _
        (nonnegative-add _ _
          (≤ℚ→≤ᵣ 0 _ (Old.upperCalls-nonnegative reports client))
          (≤ℚ→≤ᵣ 0 _ (reserve-nonnegative client)))
        (+ᵣ-rat (Old.upperCalls reports client) (reserve client)))

    requirements-cover : New.Covered requirements
    requirements-cover state member client = isTrans≤ᵣ _ _ _
      (Changes.revaluation-covers drift (λ c → rat (Old.upperCalls reports c))
        (Old.upperCalls-cover reports) state member client)
      (isTrans≤≡ᵣ _ _ _
        (≤ᵣ-o+ _ _ (newCollateral state client)
          (≤ᵣ-o+ _ _ (rat (Old.upperCalls reports client)) (reserve-bound client)))
        (cong (newCollateral state client +ᵣ_)
          (+ᵣ-rat (Old.upperCalls reports client) (reserve client))))

    module Calls = Transfers.MinimumTransfer Allowed newClaims newCollateral
      requirements requirements-nonnegative requirements-cover

    plan : Calls.Payments → Journal.Ledger → Calls.Payments
    plan mta ledger = Calls.requested mta (Journal.paid ledger)

    plan-nonnegative : ∀ mta ledger → Calls.NonnegativePayments (plan mta ledger)
    plan-nonnegative mta ledger = Calls.requested-nonnegative mta (Journal.paid ledger)

    -- This is a per-client receipt condition, not a sum of message amounts.
    -- Repeated event IDs contribute no additional newlyPaid cash.
    PlanSettled : Calls.Payments → Journal.Ledger → Journal.Batch → Type₀
    PlanSettled mta ledger batch = ∀ client →
      plan mta ledger client ℚ.≤ Journal.newlyPaid ledger batch client

    actual-cash-dominates : ∀ mta ledger batch → PlanSettled mta ledger batch → ∀ client →
      rat (Calls.received mta (Journal.paid ledger) client)
        ≤ᵣ rat (Journal.paid (Journal.ingestBatch ledger batch) client)
    actual-cash-dominates mta ledger batch settled client = isTrans≡≤ᵣ _ _ _
      (sym (+ᵣ-rat (Journal.paid ledger client) (plan mta ledger client)))
      (isTrans≤≡ᵣ _ _ _
        (≤ᵣ-o+ _ _ (rat (Journal.paid ledger client))
          (≤ℚ→≤ᵣ _ _ (settled client)))
        (sym (Journal.paid-ingestBatch-accounting ledger batch client)))

    effectiveCollateral : Journal.Ledger → State → Vector clients
    effectiveCollateral ledger = New.posted (Journal.paid ledger)

    -- A guarantee for the current ledger under the NEW valuation snapshot.
    -- Loss is the supplied severity-weighted positive unsecured claim;
    -- it does not include FX settlement principal or liquidity loss.
    record Controlled (mta : Calls.Payments) (ledger : Journal.Ledger) : Type₀ where
      field
        cash-valid : Calls.NonnegativePayments (Journal.paid ledger)
        inventory-backed : ∀ state →
          sum (newCollateral state) ≤ᵣ Collateral.inventoryValue allocation newValuation state
        clients-covered-to-tolerance : ∀ state → Allowed state → ∀ client →
          newClaims state client ≤ᵣ effectiveCollateral ledger state client +ᵣ rat (mta client)
        client-residual-bounded : ∀ state → Allowed state → ∀ client →
          stopLoss (newClaims state client) (effectiveCollateral ledger state client) ≤ᵣ rat (mta client)
        broker-residual-bounded : ∀ state → Allowed state →
          Credit.brokerResidual (newClaims state) (effectiveCollateral ledger state) ≤ᵣ Calls.totalTolerance mta
        every-loss-bounded : (severity : State → Credit.Severity clients) → ∀ state → Allowed state →
          Credit.realizedCloseoutLoss (newClaims state) (effectiveCollateral ledger state) (severity state)
            ≤ᵣ Calls.totalTolerance mta
    open Controlled public

    controller-correct : ∀ mta → Calls.NonnegativePayments mta → ∀ ledger batch →
      PlanSettled mta ledger batch → Controlled mta (Journal.ingestBatch ledger batch)
    controller-correct mta mta₊ ledger batch settled .cash-valid =
      Journal.paid-nonnegative (Journal.ingestBatch ledger batch)
    controller-correct mta mta₊ ledger batch settled .inventory-backed =
      Collateral.total-eligible≤inventory allocation newValuation
    controller-correct mta mta₊ ledger batch settled .clients-covered-to-tolerance state member client =
      isTrans≤ᵣ _ _ _ (Calls.coverage-with-tolerance mta mta₊ (Journal.paid ledger) state member client)
        (≤ᵣ-+o _ _ (rat (mta client))
          (≤ᵣ-o+ _ _ (newCollateral state client) (actual-cash-dominates mta ledger batch settled client)))
    controller-correct mta mta₊ ledger batch settled .client-residual-bounded state member client =
      stopLoss-upper _ _ _ (≤ℚ→≤ᵣ 0 (mta client) (mta₊ client))
        (clients-covered-to-tolerance (controller-correct mta mta₊ ledger batch settled) state member client)
    controller-correct mta mta₊ ledger batch settled .broker-residual-bounded state member =
      Credit.residual-budget _ _ _
        (client-residual-bounded (controller-correct mta mta₊ ledger batch settled) state member)
    controller-correct mta mta₊ ledger batch settled .every-loss-bounded severity state member =
      isTrans≤ᵣ _ _ _ (Credit.loss≤brokerResidual _ _ (severity state))
        (broker-residual-bounded (controller-correct mta mta₊ ledger batch settled) state member)

    -- Executable gate over rational amounts. Failure proves an unfulfilled
    -- plan, not economic insolvency: requirements may be conservative.
    data SettlementResult (mta : Calls.Payments) (ledger : Journal.Ledger)
      (batch : Journal.Batch) : Type₀ where
      completed : PlanSettled mta ledger batch → Controlled mta (Journal.ingestBatch ledger batch) →
        SettlementResult mta ledger batch
      awaiting-receipts : (client : Fin clients) →
        ¬ (plan mta ledger client ℚ.≤ Journal.newlyPaid ledger batch client) → SettlementResult mta ledger batch

    settle : ∀ mta → Calls.NonnegativePayments mta → ∀ ledger batch → SettlementResult mta ledger batch
    settle mta mta₊ ledger batch with ∀Dec
      (λ client → plan mta ledger client ℚ.≤ Journal.newlyPaid ledger batch client)
      (λ client → ℚ.≤Dec (plan mta ledger client) (Journal.newlyPaid ledger batch client))
    ... | inl settled = completed settled (controller-correct mta mta₊ ledger batch settled)
    ... | inr (client , insufficient) = awaiting-receipts client insufficient

    -- Zero tolerance specializes the system theorem to complete per-client
    -- coverage and zero broker residual/default loss for every severity.
    zero-mta-book-guarantee : ∀ ledger batch → PlanSettled Calls.zeroMTA ledger batch →
      New.BookGuarantee (Journal.paid (Journal.ingestBatch ledger batch))
    zero-mta-book-guarantee ledger batch settled = New.guarantee _ λ state member client →
      isTrans≤≡ᵣ _ _ _
        (clients-covered-to-tolerance
          (controller-correct Calls.zeroMTA (λ _ → ℚ.decℚ≤?) ledger batch settled) state member client)
        (+IdR (effectiveCollateral (Journal.ingestBatch ledger batch) state client))

    -- Cubical paths identify the ledger after replay and transport the full
    -- dependent certificate, so cached control evidence survives replay.
    plan-replay : ∀ mta ledger batch →
      plan mta (Journal.ingestBatch (Journal.ingestBatch ledger batch) batch)
        ≡ plan mta (Journal.ingestBatch ledger batch)
    plan-replay mta ledger batch = cong (plan mta) (Journal.ingestBatch-replay ledger batch)

    controlled-replay : ∀ mta ledger batch → Controlled mta (Journal.ingestBatch ledger batch) →
      Controlled mta (Journal.ingestBatch (Journal.ingestBatch ledger batch) batch)
    controlled-replay mta ledger batch =
      subst (Controlled mta) (sym (Journal.ingestBatch-replay ledger batch))

    controlled-same-events : ∀ mta ledger first second →
      (∀ event → Journal.batchMask first event ≡ Journal.batchMask second event) →
      Controlled mta (Journal.ingestBatch ledger first) → Controlled mta (Journal.ingestBatch ledger second)
    controlled-same-events mta ledger first second same =
      subst (Controlled mta) (Journal.ingestBatch-same-events ledger first second same)

    -- The inventory bound composes with additional recorded cash, without
    -- allowing one client's surplus to discharge another client's exposure.
    resources : Journal.Ledger → State → ℝ
    resources ledger state = Collateral.inventoryValue allocation newValuation state
      +ᵣ sum (λ client → rat (Journal.paid ledger client))

    effective-collateral-backed : ∀ ledger state →
      sum (effectiveCollateral ledger state) ≤ᵣ resources ledger state
    effective-collateral-backed ledger state = isTrans≡≤ᵣ _ _ _
      (sum-add (newCollateral state) (λ client → rat (Journal.paid ledger client)))
      (≤ᵣ-+o _ _ (sum (λ client → rat (Journal.paid ledger client)))
        (Collateral.total-eligible≤inventory allocation newValuation state))

    positive-claims-backed : ∀ mta → Calls.NonnegativePayments mta → ∀ ledger → Controlled mta ledger →
      ∀ state → Allowed state → sum (λ client → positivePart (newClaims state client))
        ≤ᵣ resources ledger state +ᵣ Calls.totalTolerance mta
    positive-claims-backed mta mta₊ ledger certificate state member = isTrans≤ᵣ _ _ _
      (sum-monotone _ _ (λ client → positivePart-upper _ _
        (clients-covered-to-tolerance certificate state member client)
        (nonnegative-add _ _
          (nonnegative-add _ _ (Collateral.eligible-nonnegative allocation newValuation state client)
            (≤ℚ→≤ᵣ 0 _ (Journal.paid-nonnegative ledger client)))
          (≤ℚ→≤ᵣ 0 _ (mta₊ client)))))
      (isTrans≡≤ᵣ _ _ _ (sum-add (effectiveCollateral ledger state) (λ client → rat (mta client)))
        (≤ᵣ-+o _ _ (Calls.totalTolerance mta) (effective-collateral-backed ledger state)))

    -- Control evidence is propositional; changing proof construction cannot
    -- change the certified state. This also gives paths of whole records.
    controlled-isProp : ∀ mta ledger → isProp (Controlled mta ledger)
    controlled-isProp mta ledger left right i .cash-valid client =
      ℚ.isProp≤ _ _ (cash-valid left client) (cash-valid right client) i
    controlled-isProp mta ledger left right i .inventory-backed state =
      isProp≤ᵣ _ _ (inventory-backed left state) (inventory-backed right state) i
    controlled-isProp mta ledger left right i .clients-covered-to-tolerance state member client =
      isProp≤ᵣ _ _ (clients-covered-to-tolerance left state member client)
        (clients-covered-to-tolerance right state member client) i
    controlled-isProp mta ledger left right i .client-residual-bounded state member client =
      isProp≤ᵣ _ _ (client-residual-bounded left state member client) (client-residual-bounded right state member client) i
    controlled-isProp mta ledger left right i .broker-residual-bounded state member =
      isProp≤ᵣ _ _ (broker-residual-bounded left state member) (broker-residual-bounded right state member) i
    controlled-isProp mta ledger left right i .every-loss-bounded severity state member =
      isProp≤ᵣ _ _ (every-loss-bounded left severity state member) (every-loss-bounded right severity state member) i

    -- Pointwise ledger equality lifts to equality of ledger + certificate,
    -- including any independently reconstructed proof after replay.
    certified-state-replay : ∀ mta ledger batch
      (before : Controlled mta (Journal.ingestBatch ledger batch))
      (after : Controlled mta (Journal.ingestBatch (Journal.ingestBatch ledger batch) batch)) →
      Path (Σ Journal.Ledger (Controlled mta))
        (Journal.ingestBatch (Journal.ingestBatch ledger batch) batch , after)
        (Journal.ingestBatch ledger batch , before)
    certified-state-replay mta ledger batch before after =
      Σ≡Prop (controlled-isProp mta) (Journal.ingestBatch-replay ledger batch)
