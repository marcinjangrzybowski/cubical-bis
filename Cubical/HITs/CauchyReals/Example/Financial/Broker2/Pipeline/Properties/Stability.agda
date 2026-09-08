{-# OPTIONS --safe --cubical #-}

-- Receipt replay and reordering preserve the concrete pipeline state and
-- its dependent risk certificate. The valuation is fixed across these
-- receipt transitions; no commutation of market updates is asserted.
module Cubical.HITs.CauchyReals.Example.Financial.Broker2.Pipeline.Properties.Stability where

open import Cubical.HITs.CauchyReals.Example.Financial.Core.Finite
open import Cubical.HITs.CauchyReals.Foundation.Rationals using (ℚ; module ℚ)
open import Cubical.Data.Sigma.Properties using (Σ≡Prop)
open import Cubical.HITs.CauchyReals.Example.Financial.Broker2.Pipeline.Properties.FiniteRisk
import Cubical.HITs.CauchyReals.Example.Financial.Broker2.Pipeline.Implementation.Sources as Source
import Cubical.HITs.CauchyReals.Example.Financial.Broker2.Pipeline.Properties.Correctness as Execution
import Cubical.HITs.CauchyReals.Example.Financial.Broker2.V05Tolerance as Tolerance
import Cubical.HITs.CauchyReals.Example.Financial.Broker2.V04Rational as Rational
import Cubical.HITs.CauchyReals.Example.Financial.Broker.Stage07Calls as Transfers

module Stability {clients trades instruments lots assets receipts stresses : ℕ}
  (sources : Source.Schema.DataSources clients trades instruments lots assets receipts stresses) where
  module Engine = Execution.Pipeline sources
  open Engine using (State; valuation; ledger)

  state-path : ∀ s t → valuation s ≡ valuation t → ledger s ≡ ledger t → s ≡ t
  state-path s t valuations ledgers i .valuation = valuations i
  state-path s t valuations ledgers i .ledger = ledgers i

  receive-replay : ∀ s next deliveries →
    Engine.receive (Engine.receive s next deliveries) next deliveries
      ≡ Engine.receive s next deliveries
  receive-replay s next deliveries = state-path _ _ refl
    (Engine.Cash.receiveLedger-replay (ledger s) deliveries)

  receive-commutes : ∀ s next first second →
    Engine.receive (Engine.receive s next first) next second
      ≡ Engine.receive (Engine.receive s next second) next first
  receive-commutes s next first second = state-path _ _ refl
    (Engine.Cash.receiveLedger-commutes (ledger s) first second)

  guarantee-isProp : ∀ s mta → isProp (Engine.Guarantee s mta)
  guarantee-isProp s mta = Tolerance.guarantee-isProp
    (Engine.Abstract.view (Engine.referenceState s)) mta

  -- The public guarantee uses independent indexed source sums. The paths
  -- therefore preserve that economic specification, including rebuilt proofs.
  certified-state-replay : ∀ s next deliveries mta
    (before : Engine.Guarantee (Engine.receive s next deliveries) mta)
    (after : Engine.Guarantee (Engine.receive (Engine.receive s next deliveries) next deliveries) mta) →
    Path (Σ State (λ t → Engine.Guarantee t mta))
      (Engine.receive (Engine.receive s next deliveries) next deliveries , after)
      (Engine.receive s next deliveries , before)
  certified-state-replay s next deliveries mta before after =
    Σ≡Prop (λ t → guarantee-isProp t mta) (receive-replay s next deliveries)

  certified-state-commutes : ∀ s next first second mta
    (forward : Engine.Guarantee (Engine.receive (Engine.receive s next first) next second) mta)
    (backward : Engine.Guarantee (Engine.receive (Engine.receive s next second) next first) mta) →
    Path (Σ State (λ t → Engine.Guarantee t mta))
      (Engine.receive (Engine.receive s next first) next second , forward)
      (Engine.receive (Engine.receive s next second) next first , backward)
  certified-state-commutes s next first second mta forward backward =
    Σ≡Prop (λ t → guarantee-isProp t mta) (receive-commutes s next first second)

  -- With unchanged valuation, each computed positive-change sum vanishes.
  -- This is a symbolic regression theorem over arbitrary source catalogs.
  reserve-unchanged : ∀ s → Engine.reserve s (valuation s) ≡ (λ _ → 0)
  reserve-unchanged s = funExt (λ client → cong₂ ℚ._+_
    (differenceReserve-self (λ scenario → Engine.Values.claimTotals (valuation s) scenario client))
    (differenceReserve-self (λ scenario → Engine.Values.collateralTotals (valuation s) scenario client))
    ∙ ℚ.+IdL 0)

  -- The concrete quote then agrees with V06 before any revaluation reserve.
  -- This identifies amounts, not arbitrary conservative report records.
  quote-refines-unchanged : ∀ s report mta →
    Engine.Code.quoteCall s (Rational.amounts report) (valuation s) mta
      ≡ Engine.Abstract.Old.quoteCall (Engine.decode s) report mta
  quote-refines-unchanged s report mta =
    Engine.quote-refines-model s report (valuation s) mta
    ∙ funExt (λ client →
      cong (λ amount → Transfers.transferAmount amount (mta client))
        (cong (Rational.amounts report client ℚ.+_)
          (funExt⁻ (reserve-unchanged s) client)
          ∙ ℚ.+IdR (Rational.amounts report client)))
