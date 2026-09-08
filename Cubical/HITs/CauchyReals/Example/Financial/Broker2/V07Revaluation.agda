{-# OPTIONS --safe --cubical #-}

-- Version 7: the same receipt engine survives a certified market update.
-- Cash is preserved; an incremental report is refreshed by an adverse-move
-- reserve, then the existing quote/receive/process workflow is used again.
module Cubical.HITs.CauchyReals.Example.Financial.Broker2.V07Revaluation where

open import Cubical.HITs.CauchyReals.Example.Financial.Core.Finite public
open import Cubical.HITs.CauchyReals.Foundation.Rationals using (ℚ; module ℚ)
open import Cubical.Data.Unit using (Unit; tt)
import Cubical.HITs.CauchyReals.Example.Financial.Broker2.V06Receipts as Previous
import Cubical.HITs.CauchyReals.Example.Financial.Broker2.V05Tolerance as Tolerance
import Cubical.HITs.CauchyReals.Example.Financial.Broker2.V04Rational as Rational
import Cubical.HITs.CauchyReals.Example.Financial.Broker2.V03Stress as Stress
import Cubical.HITs.CauchyReals.Example.Financial.Broker2.V02Clients as Clients
import Cubical.HITs.CauchyReals.Example.Financial.Broker.Stage06Revaluation as Repricing
import Cubical.HITs.CauchyReals.Example.Financial.Broker.Stage07Calls as Transfers
import Cubical.HITs.CauchyReals.Example.Financial.Margin.Base as Margin

open Previous using (EventCatalog; Payments; Nonnegative; zeroMTA) public

module Engine {clients stresses events : ℕ} (catalog : EventCatalog events clients) where
  module Old = Previous.Engine {stresses = stresses} catalog
  module Changes = Repricing.Revaluation {clients = clients} {State = Fin (suc stresses)} (λ _ → Unit)
  open Old using (State; Report; Guarantee; view; market; ledger; engine-state; module Journal) public

  revalue : State → Stress.Market clients stresses → State
  revalue s nextMarket = engine-state nextMarket (ledger s)

  effectiveCollateral : State → Fin (suc stresses) → Vector clients
  effectiveCollateral s scenario = Clients.cash (Stress.view (view s) scenario)

  -- Claim and collateral changes are paired at each stress. No stochastic
  -- independence or forecast accuracy is inferred from these supplied bounds.
  record Update (s : State) : Type₀ where
    field
      nextMarket : Stress.Market clients stresses
      drift : Changes.DriftBounds (Stress.claims (market s)) (effectiveCollateral s)
        (Stress.claims nextMarket) (effectiveCollateral (revalue s nextMarket))
      reserve : Payments clients
      reserve-nonnegative : Nonnegative reserve
      reserve-bound : ∀ client → Changes.driftReserve drift client ≤ᵣ rat (reserve client)
  open Update public

  -- Every report is an upper bound on the CURRENT INCREMENTAL requirement.
  -- The preserved journal cash is already included in effectiveCollateral.
  -- We add the reserve here, and never subtract the existing cash again.
  refreshReport : ∀ s → Report s → (change : Update s) → Report (revalue s (nextMarket change))
  refreshReport s report change .Rational.amounts client =
    Rational.amounts report client ℚ.+ reserve change client
  refreshReport s report change .Rational.amounts-nonnegative client = ≤ᵣ→≤ℚ 0 _
    (isTrans≤≡ᵣ _ _ _
      (nonnegative-add _ _
        (≤ℚ→≤ᵣ 0 _ (Rational.amounts-nonnegative report client))
        (≤ℚ→≤ᵣ 0 _ (reserve-nonnegative change client)))
      (+ᵣ-rat (Rational.amounts report client) (reserve change client)))
  refreshReport s report change .Rational.dominates client =
    Margin.margin-least (Stress.scenarioClaims (view next) client)
      (Stress.scenarioCollateral (view next) client)
      (rat (Rational.amounts report client ℚ.+ reserve change client))
      (≤ℚ→≤ᵣ 0 _ (Rational.amounts-nonnegative (refreshReport s report change) client))
      (λ scenario → new-cover scenario tt client)
    where
    next = revalue s (nextMarket change)

    old-cover : Changes.CashCoverage (Stress.claims (market s)) (effectiveCollateral s)
      (Rational.toReal (Rational.amounts report))
    old-cover scenario _ client = isTrans≤≡ᵣ _ _ _
      (Rational.report-covers (view s) report scenario client)
      (+ᵣAssoc (Stress.collateral (market s) scenario client) (Stress.cash (view s) client)
        (rat (Rational.amounts report client)))

    new-cover : Changes.CashCoverage (Stress.claims (nextMarket change)) (effectiveCollateral next)
      (λ client → rat (Rational.amounts report client ℚ.+ reserve change client))
    new-cover scenario member client = isTrans≤ᵣ _ _ _
      (Changes.revaluation-covers (drift change) (Rational.toReal (Rational.amounts report)) old-cover scenario member client)
      (isTrans≤≡ᵣ _ _ _
        (≤ᵣ-o+ _ _ (effectiveCollateral next scenario client)
          (≤ᵣ-o+ _ _ (rat (Rational.amounts report client)) (reserve-bound change client)))
        (cong (effectiveCollateral next scenario client +ᵣ_)
          (+ᵣ-rat (Rational.amounts report client) (reserve change client))))

  quoteCall : ∀ s → Report s → Update s → Payments clients → Payments clients
  quoteCall s report change mta = Old.quoteCall (revalue s (nextMarket change)) (refreshReport s report change) mta

  receive : ∀ s → Update s → Journal.Batch → State
  receive s change batch = Old.receive (revalue s (nextMarket change)) batch

  Adequate : ∀ s → Report s → Update s → Payments clients → Journal.Batch → Type₀
  Adequate s report change mta batch =
    Old.Adequate (revalue s (nextMarket change)) (refreshReport s report change) mta batch

  -- The presentation's final contract: any book size, every supplied stress,
  -- every severity, actual newly credited receipts, under a proved update.
  receive-correct : ∀ s report change mta → Nonnegative mta → ∀ batch →
    Adequate s report change mta batch → Guarantee (receive s change batch) mta
  receive-correct s report change mta mta₊ batch =
    Old.receive-correct (revalue s (nextMarket change)) (refreshReport s report change) mta mta₊ batch

  -- Process returns both the assessment and the updated report for the NEXT
  -- cycle. That report can itself be passed to another market update.
  process : ∀ s report change mta → Nonnegative mta → ∀ batch →
    Old.Processed (revalue s (nextMarket change)) (refreshReport s report change) mta batch
  process s report change mta mta₊ batch =
    Old.process (revalue s (nextMarket change)) (refreshReport s report change) mta mta₊ batch

  zero-mta-safe : ∀ s report change batch → Adequate s report change zeroMTA batch →
    Stress.Safe (view (receive s change batch))
  zero-mta-safe s report change batch =
    Old.zero-mta-safe (revalue s (nextMarket change)) (refreshReport s report change) batch

  zero-mta-loss-zero : ∀ s report change batch → Adequate s report change zeroMTA batch →
    ∀ scenario θ → Stress.loss (view (receive s change batch)) scenario θ ≡ 0
  zero-mta-loss-zero s report change batch enough =
    Stress.safe-loss-zero (view (receive s change batch)) (zero-mta-safe s report change batch enough)

  -- This special case supplies the regression contract, not a numeric market
  -- example: it holds for EVERY state of the previous engine.
  unchanged : ∀ s → Update s
  unchanged s .nextMarket = market s
  unchanged s .drift .Changes.claimShock _ = 0
  unchanged s .drift .Changes.collateralDrop _ = 0
  unchanged s .drift .Changes.claimShock-nonnegative _ = ≤ᵣ-refl 0
  unchanged s .drift .Changes.collateralDrop-nonnegative _ = ≤ᵣ-refl 0
  unchanged s .drift .Changes.claim-rise scenario _ client =
    isTrans≤≡ᵣ _ _ _ (≤ᵣ-refl _) (sym (+IdR (Stress.claims (market s) scenario client)))
  unchanged s .drift .Changes.collateral-fall scenario _ client =
    isTrans≤≡ᵣ _ _ _ (≤ᵣ-refl _) (sym (+IdR (effectiveCollateral s scenario client)))
  unchanged s .reserve _ = 0
  unchanged s .reserve-nonnegative _ = ℚ.isRefl≤ 0
  unchanged s .reserve-bound _ = isTrans≡≤ᵣ _ _ _ (+IdL 0) (≤ᵣ-refl 0)

  quote-refines-V06 : ∀ s report mta → quoteCall s report (unchanged s) mta ≡ Old.quoteCall s report mta
  quote-refines-V06 s report mta = funExt (λ client →
    cong (λ amount → Transfers.transferAmount amount (mta client)) (ℚ.+IdR (Rational.amounts report client)))

  receive-refines-V06 : ∀ s batch → receive s (unchanged s) batch ≡ Old.receive s batch
  receive-refines-V06 s batch = refl

  revalue-preserves-ledger : ∀ s nextMarket → ledger (revalue s nextMarket) ≡ ledger s
  revalue-preserves-ledger s nextMarket = refl

  receipt-replay : ∀ s change batch → Old.receive (receive s change batch) batch ≡ receive s change batch
  receipt-replay s change batch = Old.receive-replay (revalue s (nextMarket change)) batch

  certified-state-replay : ∀ s change batch mta
    (before : Guarantee (receive s change batch) mta)
    (after : Guarantee (Old.receive (receive s change batch) batch) mta) →
    Path (Σ State (λ t → Guarantee t mta))
      (Old.receive (receive s change batch) batch , after) (receive s change batch , before)
  certified-state-replay s change batch mta =
    Old.certified-state-replay (revalue s (nextMarket change)) batch mta
