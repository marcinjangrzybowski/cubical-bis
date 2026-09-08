{-# OPTIONS --safe --cubical #-}

-- Version 5: allow small transfers to remain outstanding within an explicit
-- minimum transfer amount (MTA). The state and its incremental rational report
-- are inherited from V04; each client receives a separate rational threshold.
--
-- quoteCall requests zero when the reported amount is at most the MTA,
-- including equality. Otherwise it requests the entire reported amount.
-- receive and advanceReport retain V04's behavior: only actual new receipts
-- increase cash or reduce the remaining report. Suppression credits no cash.
--
-- For nonnegative MTAs and receipts, receive-correct proves that meeting each
-- request leaves every client shortfall at most its MTA in every supplied
-- scenario. Guarantee adds bounds on aggregate positive exposure and every
-- severity-weighted closeout loss by the sum of the client MTAs.
-- assess returns this guarantee on success or identifies an unmet request.
-- An unmet request need not imply that the tolerated exposure bound fails.
--
-- receive-refines-V04 preserves the earlier state transition exactly.
-- zero-mta-refines-V04 recovers the V04 quote when all MTAs are zero, and
-- zero-mta-safe recovers full coverage. Positive MTAs permit nonzero residuals.
-- The full-amount-or-zero rule and its equality boundary are explicit policy
-- choices; no regulatory threshold or probabilistic loss estimate is supplied.
module Cubical.HITs.CauchyReals.Example.Financial.Broker2.V05Tolerance where

open import Cubical.HITs.CauchyReals.Example.Financial.Core.Finite public
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.Shortfall
open import Cubical.HITs.CauchyReals.Foundation.Rationals using (ℚ; module ℚ)
open import Cubical.Relation.Nullary using (yes; no; ¬_)
open import Cubical.Data.FinData.Properties using (∀Dec)
open import Cubical.Data.Sum.Base using (inl; inr)
import Cubical.HITs.CauchyReals.Example.Financial.Broker2.V04Rational as Previous
import Cubical.HITs.CauchyReals.Example.Financial.Broker2.V03Stress as Stress
import Cubical.HITs.CauchyReals.Example.Financial.Broker2.V02Clients as Clients
import Cubical.HITs.CauchyReals.Example.Financial.Broker.Stage07Calls as Transfers
import Cubical.HITs.CauchyReals.Example.Financial.Margin.CounterpartyRisk as Credit

open Previous using (State; Market; Report; Payments; Nonnegative; toReal; toReal-nonnegative;
  receive; advanceReport; amounts; amounts-nonnegative; dominates) public

quoteCall : ∀ {clients stresses} (b : State clients stresses) → Report b → Payments clients → Payments clients
quoteCall b report mta client = Transfers.transferAmount (amounts report client) (mta client)

quote-nonnegative : ∀ {clients stresses} (b : State clients stresses) report mta →
  Nonnegative (quoteCall b report mta)
quote-nonnegative b report mta client = Transfers.transferAmount-nonnegative _ _ (amounts-nonnegative report client)

Adequate : ∀ {clients stresses} (b : State clients stresses) → Report b → Payments clients → Payments clients → Type₀
Adequate b report mta paid = ∀ client → quoteCall b report mta client ℚ.≤ paid client

Bounded : ∀ {clients stresses} → State clients stresses → Payments clients → Type₀
Bounded b mta = ∀ scenario client →
  stopLoss (Clients.claims (Stress.view b scenario) client) (Clients.cash (Stress.view b scenario) client)
    ≤ᵣ rat (mta client)

coverage-with-tolerance : ∀ {clients stresses} (b : State clients stresses) report mta → Nonnegative mta →
  ∀ paid paid₊ → Adequate b report mta paid → ∀ scenario client →
  Clients.claims (Stress.view b scenario) client
    ≤ᵣ Clients.cash (Stress.view (receive b paid paid₊) scenario) client +ᵣ rat (mta client)
coverage-with-tolerance b report mta mta₊ paid paid₊ enough scenario client =
  isTrans≤ᵣ _ _ _ old-cover (isTrans≤≡ᵣ _ _ _
    (≤ᵣ-o+ _ _ C (isTrans≤ᵣ _ _ _
      (Transfers.transferAmount-tolerance (amounts report client) (mta client) (mta₊ client))
      (≤ᵣ-+o _ _ (rat (mta client)) (≤ℚ→≤ᵣ _ _ (enough client)))))
    (+ᵣAssoc C (rat (paid client)) (rat (mta client))
      ∙ cong (_+ᵣ rat (mta client))
        (sym (+ᵣAssoc (Stress.collateral (Stress.market b) scenario client) (Stress.cash b client) (rat (paid client))))))
  where
  C = Clients.cash (Stress.view b scenario) client
  old-cover : Clients.claims (Stress.view b scenario) client ≤ᵣ C +ᵣ rat (amounts report client)
  old-cover = isTrans≤≡ᵣ _ _ _ (Previous.report-covers b report scenario client)
    (+ᵣAssoc (Stress.collateral (Stress.market b) scenario client) (Stress.cash b client) (rat (amounts report client)))

receive-correct : ∀ {clients stresses} (b : State clients stresses) report mta → Nonnegative mta →
  ∀ paid paid₊ → Adequate b report mta paid → Bounded (receive b paid paid₊) mta
receive-correct b report mta mta₊ paid paid₊ enough scenario client =
  stopLoss-upper _ _ _ (≤ℚ→≤ᵣ 0 _ (mta₊ client))
    (coverage-with-tolerance b report mta mta₊ paid paid₊ enough scenario client)

record Guarantee {clients stresses} (b : State clients stresses) (mta : Payments clients) : Type₀ where
  field
    clients-bounded : Bounded b mta
    broker-bounded : ∀ scenario → Stress.residual b scenario ≤ᵣ sum (toReal mta)
    every-loss-bounded : ∀ scenario (θ : Credit.Severity clients) → Stress.loss b scenario θ ≤ᵣ sum (toReal mta)
open Guarantee public

guarantee : ∀ {clients stresses} (b : State clients stresses) mta → Bounded b mta → Guarantee b mta
guarantee b mta bound .clients-bounded = bound
guarantee b mta bound .broker-bounded scenario = Credit.residual-budget _ _ _ (bound scenario)
guarantee b mta bound .every-loss-bounded scenario θ = isTrans≤ᵣ _ _ _
  (Credit.loss≤brokerResidual (Clients.claims (Stress.view b scenario)) (Clients.cash (Stress.view b scenario)) θ)
  (broker-bounded (guarantee b mta bound) scenario)

data Assessment {clients stresses} (b : State clients stresses) (report : Report b)
  (mta paid : Payments clients) (paid₊ : Nonnegative paid) : Type₀ where
  controlled : Adequate b report mta paid → Guarantee (receive b paid paid₊) mta → Assessment b report mta paid paid₊
  unmet-quote : (client : Fin clients) → ¬ (quoteCall b report mta client ℚ.≤ paid client) → Assessment b report mta paid paid₊

assess : ∀ {clients stresses} (b : State clients stresses) report mta → Nonnegative mta →
  ∀ paid paid₊ → Assessment b report mta paid paid₊
assess b report mta mta₊ paid paid₊ with ∀Dec (λ client → quoteCall b report mta client ℚ.≤ paid client)
  (λ client → ℚ.≤Dec (quoteCall b report mta client) (paid client))
... | inl enough = controlled enough
  (guarantee (receive b paid paid₊) mta (receive-correct b report mta mta₊ paid paid₊ enough))
... | inr (client , insufficient) = unmet-quote client insufficient

zeroMTA : ∀ {clients} → Payments clients
zeroMTA _ = 0

private
  transfer-zero : ∀ gap → 0 ℚ.≤ gap → Transfers.transferAmount gap 0 ≡ gap
  transfer-zero gap gap₊ with ℚ.≤Dec gap 0
  ... | yes gap≤0 = sym (ℚ.isAntisym≤ gap 0 gap≤0 gap₊)
  ... | no _ = refl

zero-mta-refines-V04 : ∀ {clients stresses} (b : State clients stresses) report →
  quoteCall b report zeroMTA ≡ Previous.quoteCall b report
zero-mta-refines-V04 b report = funExt (λ client → transfer-zero _ (amounts-nonnegative report client))

receive-refines-V04 : ∀ {clients stresses} (b : State clients stresses) paid paid₊ →
  receive b paid paid₊ ≡ Previous.receive b paid paid₊
receive-refines-V04 b paid paid₊ = refl

zero-mta-safe : ∀ {clients stresses} (b : State clients stresses) report paid paid₊ →
  Adequate b report zeroMTA paid → Stress.Safe (receive b paid paid₊)
zero-mta-safe b report paid paid₊ enough = Previous.receive-correct b report paid paid₊
  (λ client → subst (λ q → q ℚ.≤ paid client) (funExt⁻ (zero-mta-refines-V04 b report) client) (enough client))

guarantee-isProp : ∀ {clients stresses} (b : State clients stresses) mta → isProp (Guarantee b mta)
guarantee-isProp b mta left right i .clients-bounded scenario client =
  isProp≤ᵣ _ _ (clients-bounded left scenario client) (clients-bounded right scenario client) i
guarantee-isProp b mta left right i .broker-bounded scenario =
  isProp≤ᵣ _ _ (broker-bounded left scenario) (broker-bounded right scenario) i
guarantee-isProp b mta left right i .every-loss-bounded scenario θ =
  isProp≤ᵣ _ _ (every-loss-bounded left scenario θ) (every-loss-bounded right scenario θ) i
