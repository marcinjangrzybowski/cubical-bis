{-# OPTIONS --safe --cubical #-}

-- End-to-end broker controls for the supplied swap book and joint real box.
-- Methodological context: ../../REFERENCES.md#ben-tal-nemirovski-1998 and
-- ../../REFERENCES.md#bcbs-settlement-2013. Quotes and calls are synthetic;
-- receipts and native-currency funding are separate available balances.

module Cubical.HITs.CauchyReals.Example.Financial.Examples.FX.BrokerGuarantees where

open import Cubical.HITs.CauchyReals.Example.Financial.Core.Finite
open import Cubical.HITs.CauchyReals.Example.Financial.Core.Vectors using (two)
open import Cubical.HITs.CauchyReals.Example.Financial.Instruments.FXBounds
open import Cubical.HITs.CauchyReals.Foundation.Rationals using (ℚ; module ℚ; [_/_])
open import Cubical.Data.NatPlusOne using (fromNatℕ₊₁)
open import Cubical.Data.Int.Base using (fromNatℤ)
open import Cubical.Data.Sigma using (_×_; Σ≡Prop)
open import Cubical.Data.List.Base using ([]; _∷_)
open import Cubical.Data.Empty using (⊥; isProp⊥)
import Cubical.Data.Empty as Empty
open import Cubical.Data.Bool using (Bool; true; false; isSetBool; false≢true)
open import Cubical.Relation.Nullary using (Dec; yes; no; ¬_)
open import Cubical.Foundations.Equiv using (_≃_; propBiimpl→Equiv)
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
import Cubical.Data.FinData.Base as F
import Cubical.HITs.CauchyReals.Example.Financial.Margin.Scenario as Scenario
import Cubical.HITs.CauchyReals.Example.Financial.Margin.Workflow as Workflow
import Cubical.HITs.CauchyReals.Example.Financial.Margin.PaymentHistory as History
import Cubical.HITs.CauchyReals.Example.Financial.Margin.MarginControl as Control
import Cubical.HITs.CauchyReals.Example.Financial.Margin.CounterpartyRisk as Credit
import Cubical.HITs.CauchyReals.Example.Financial.Settlement.Base as Settlement
import Cubical.HITs.CauchyReals.Example.Financial.Examples.FX.BrokerMargin as B
import Cubical.HITs.CauchyReals.Example.Financial.Examples.FX.BrokerOperations as Operations
import Cubical.HITs.CauchyReals.Example.Financial.Examples.FX.JointFXMargin as Joint

-- Client coordinates are retained from portfolio valuation through payment.
claims collateral : FXState → Vector 2
claims state = two (Joint.claimAtA state) (Joint.claimAtB state)
collateral state = two 5 (Joint.collateralAtB state)

clientHoldings : Fin 2 → Vector 2
clientHoldings = two B.holdingsA B.holdingsB

tradeClaims : FXState → Vector 2
tradeClaims state client =
  sum (λ trade → clientHoldings client trade ·ᵣ farValue (B.swaps trade) state)

trade-claims-agree : ∀ state → tradeClaims state ≡ claims state
trade-claims-agree state = funExt λ
  { F.zero → Joint.portfolio-A-at state
  ; (F.suc F.zero) → Joint.portfolio-B-at state
  }

calls : Fin 2 → ℚ
calls = two 25 [ 108 / 5 ]

certificates : ∀ client → Scenario.MarginCertificate (InBox Joint.box)
  (λ state → claims state client) (λ state → collateral state client) (rat (calls client))
certificates F.zero = Joint.jointCertificateA
certificates (F.suc F.zero) = Joint.jointCertificateB

module MarginWorkflow = Workflow.CertifiedClients (InBox Joint.box)
  claims collateral calls certificates

-- Native currency balances are supplied separately from client collateral.
-- The actual four far-leg instructions have gross outgoing amounts 100/100.
Liquidity : Type₀
Liquidity = Fin 2 → ℚ

Funded : Liquidity → Type₀
Funded liquidity = Settlement.GrossFundingCertificate Operations.farBook
  (λ currency → rat (liquidity currency))

private
  outgoing-hundred : ∀ currency → Settlement.grossOutgoing Operations.farBook currency ≡ 100
  outgoing-hundred F.zero = funExt⁻ Operations.far-gross-outgoing F.zero
  outgoing-hundred (F.suc F.zero) = funExt⁻ Operations.far-gross-outgoing (F.suc F.zero)

  funded-from-bounds : ∀ liquidity →
    100 ℚ.≤ liquidity F.zero → 100 ℚ.≤ liquidity (F.suc F.zero) → Funded liquidity
  funded-from-bounds liquidity domestic foreign F.zero =
    isTrans≡≤ᵣ _ _ _ (outgoing-hundred F.zero) (≤ℚ→≤ᵣ _ _ domestic)
  funded-from-bounds liquidity domestic foreign (F.suc F.zero) =
    isTrans≡≤ᵣ _ _ _ (outgoing-hundred (F.suc F.zero)) (≤ℚ→≤ᵣ _ _ foreign)

  funded-forces-bound : ∀ liquidity → Funded liquidity → ∀ currency →
    100 ℚ.≤ liquidity currency
  funded-forces-bound liquidity funded currency = ≤ᵣ→≤ℚ 100 (liquidity currency)
    (isTrans≡≤ᵣ _ _ _ (sym (outgoing-hundred currency)) (funded currency))

checkFunding : ∀ liquidity → Dec (Funded liquidity)
checkFunding liquidity with ℚ.≤Dec 100 (liquidity F.zero)
... | no missing = no (λ funded → missing (funded-forces-bound liquidity funded F.zero))
... | yes domestic with ℚ.≤Dec 100 (liquidity (F.suc F.zero))
...   | no missing = no
  (λ funded → missing (funded-forces-bound liquidity funded (F.suc F.zero)))
...   | yes foreign = yes (funded-from-bounds liquidity domestic foreign)

-- A global protocol condition, not an implementation of a PvP service.
-- It ranges over each actual far-leg instruction in the settlement book.
AtomicBook : (Fin 4 → Settlement.SettlementState) → Type₀
AtomicBook states = ∀ trade → Settlement.AtomicExchange (states trade)

all-atomic-principal-zero : ∀ states → AtomicBook states →
  sum (λ trade → Settlement.settlementPrincipalLoss Operations.baseFX
    (Operations.farBook trade) (states trade)) ≡ 0
all-atomic-principal-zero states atomic = sum-cong _ (λ _ → 0)
  (λ trade → Settlement.pvp-principal-loss-zero Operations.baseFX
    (Operations.farBook trade) (states trade) (atomic trade))
  ∙ sum-zero 4

-- The business-level requirement simultaneously covers every client at
-- every real quote in the box and funds the actual gross currency payments.
Ready : MarginWorkflow.Payments → Liquidity → Type₀
Ready paid liquidity = MarginWorkflow.AllClientsCovered paid × Funded liquidity

checkBroker : ∀ paid → MarginWorkflow.NonnegativePayments paid →
  ∀ liquidity → Dec (Ready paid liquidity)
checkBroker paid paid₊ liquidity with MarginWorkflow.checkPayments paid paid₊
... | no uncovered = no (λ ready → uncovered (fst ready))
... | yes coverage with checkFunding liquidity
...   | no unfunded = no (λ ready → unfunded (snd ready))
...   | yes funded = yes (coverage , funded)

brokerReady : ∀ paid → MarginWorkflow.NonnegativePayments paid → Liquidity → Bool
brokerReady paid paid₊ liquidity with checkBroker paid paid₊ liquidity
... | yes _ = true
... | no _ = false

broker-check-sound : ∀ paid paid₊ liquidity →
  brokerReady paid paid₊ liquidity ≡ true → Ready paid liquidity
broker-check-sound paid paid₊ liquidity proof with checkBroker paid paid₊ liquidity
... | yes ready = ready
... | no refused = Empty.rec (false≢true proof)

broker-check-complete : ∀ paid paid₊ liquidity → Ready paid liquidity →
  brokerReady paid paid₊ liquidity ≡ true
broker-check-complete paid paid₊ liquidity ready with checkBroker paid paid₊ liquidity
... | yes _ = refl
... | no refused = Empty.rec (refused ready)

-- A rational program decides the entire universal requirement because
-- both its scenario margin certificates and gross-flow reports are exact.
broker-ready≃requirements : ∀ paid paid₊ liquidity →
  (brokerReady paid paid₊ liquidity ≡ true) ≃ Ready paid liquidity
broker-ready≃requirements paid paid₊ liquidity = propBiimpl→Equiv
  (isSetBool _ _)
  (isProp× (isPropΠ3 (λ _ _ _ → isProp≤ᵣ _ _))
    (Settlement.gross-funding-isProp Operations.farBook _))
  (broker-check-sound paid paid₊ liquidity) (broker-check-complete paid paid₊ liquidity)

broker-ready-policy-path : ∀ paid paid₊ liquidity →
  (brokerReady paid paid₊ liquidity ≡ true) ≡ Ready paid liquidity
broker-ready-policy-path paid paid₊ liquidity = ua (broker-ready≃requirements paid paid₊ liquidity)

-- This is the main system certificate: it refers to the actual two-swap
-- portfolios and four settlement instructions, not just aggregate call data.
record BookGuarantee (effectiveCollateral : FXState → Vector 2) (liquidity : Liquidity) : Type₀ where
  field
    swap-portfolios-covered : ∀ state → InBox Joint.box state → ∀ client →
      tradeClaims state client ≤ᵣ effectiveCollateral state client
    every-closeout-loss-zero : (severity : FXState → Credit.Severity 2) →
      ∀ state → InBox Joint.box state →
      Credit.realizedCloseoutLoss (tradeClaims state)
        (effectiveCollateral state) (severity state) ≡ 0
    gross-settlement-funded : Funded liquidity
open BookGuarantee public

BrokerGuarantee : MarginWorkflow.Payments → Liquidity → Type₀
BrokerGuarantee paid = BookGuarantee (MarginWorkflow.postedCollateral paid)

broker-end-to-end : ∀ paid paid₊ liquidity → brokerReady paid paid₊ liquidity ≡ true →
  BrokerGuarantee paid liquidity
broker-end-to-end paid paid₊ liquidity proof .swap-portfolios-covered state member client =
  isTrans≡≤ᵣ _ _ _ (funExt⁻ (trade-claims-agree state) client)
    (fst (broker-check-sound paid paid₊ liquidity proof) state member client)
broker-end-to-end paid paid₊ liquidity proof .every-closeout-loss-zero severity state member =
  Credit.covered-loss-zero (tradeClaims state) (MarginWorkflow.postedCollateral paid state)
    (severity state) (swap-portfolios-covered (broker-end-to-end paid paid₊ liquidity proof) state member)
broker-end-to-end paid paid₊ liquidity proof .gross-settlement-funded =
  snd (broker-check-sound paid paid₊ liquidity proof)

-- With the separate atomic-delivery protocol law, the sum of these two
-- modeled loss components vanishes across the whole actual broker book.
-- This is not a theorem that all market, operational, or funding costs vanish.
closeout-and-principal-zero : ∀ paid paid₊ liquidity →
  brokerReady paid paid₊ liquidity ≡ true →
  (severity : FXState → Credit.Severity 2) → ∀ state → InBox Joint.box state →
  ∀ settlementStates → AtomicBook settlementStates →
  Credit.realizedCloseoutLoss (tradeClaims state) (MarginWorkflow.postedCollateral paid state)
    (severity state)
  +ᵣ sum (λ trade → Settlement.settlementPrincipalLoss Operations.baseFX
    (Operations.farBook trade) (settlementStates trade)) ≡ 0
closeout-and-principal-zero paid paid₊ liquidity proof severity state member settlementStates atomic =
  cong₂ _+ᵣ_
    (every-closeout-loss-zero (broker-end-to-end paid paid₊ liquidity proof) severity state member)
    (all-atomic-principal-zero settlementStates atomic) ∙ +IdL 0

-- A completed request cycle is sufficient for ANY previously received
-- nonnegative client balances; it also retains the independent funding gate.
request-cycle-ready : ∀ paid paid₊ liquidity → Funded liquidity →
  brokerReady (MarginWorkflow.afterRequests paid)
    (MarginWorkflow.afterRequests-nonnegative paid paid₊) liquidity ≡ true
request-cycle-ready paid paid₊ liquidity funded = broker-check-complete
  (MarginWorkflow.afterRequests paid) (MarginWorkflow.afterRequests-nonnegative paid paid₊)
  liquidity (MarginWorkflow.afterRequests-coverage paid , funded)

oldPayments : MarginWorkflow.Payments
oldPayments = two 15 [ 68 / 5 ]

oldPayments-nonnegative : MarginWorkflow.NonnegativePayments oldPayments
oldPayments-nonnegative F.zero = ℚ.decℚ≤?
oldPayments-nonnegative (F.suc F.zero) = ℚ.decℚ≤?

fullPayments : MarginWorkflow.Payments
fullPayments = calls

fullPayments-nonnegative : MarginWorkflow.NonnegativePayments fullPayments
fullPayments-nonnegative F.zero = ℚ.decℚ≤?
fullPayments-nonnegative (F.suc F.zero) = ℚ.decℚ≤?

liquidity100 : Liquidity
liquidity100 = two 100 100

full-payments-ready : brokerReady fullPayments fullPayments-nonnegative liquidity100 ≡ true
full-payments-ready = refl

old-payments-refused : brokerReady oldPayments oldPayments-nonnegative liquidity100 ≡ false
old-payments-refused = refl

full-broker-guarantee : BrokerGuarantee fullPayments liquidity100
full-broker-guarantee = broker-end-to-end fullPayments fullPayments-nonnegative liquidity100
  full-payments-ready

additional-requests : (λ client → rat (MarginWorkflow.outstanding oldPayments client)) ≡ two 10 8
additional-requests = funExt λ { F.zero → ℝ! ; (F.suc F.zero) → ℝ! }

additional-total : MarginWorkflow.totalOutstanding oldPayments ≡ 18
additional-total = cong sum additional-requests ∙ ℝ!

-- The minimum is over arbitrary real further receipts assigned to their
-- client netting sets, not just over a rational grid or a pooled cash total.
eighteen-is-least-further-cash : (further : Vector 2) → (∀ client → 0 ≤ᵣ further client) →
  (∀ state → InBox Joint.box state → ∀ client →
    tradeClaims state client ≤ᵣ MarginWorkflow.postedCollateral oldPayments state client +ᵣ further client) →
  18 ≤ᵣ sum further
eighteen-is-least-further-cash further further₊ coverage = isTrans≡≤ᵣ _ _ _ (sym additional-total)
  (MarginWorkflow.requests-total-minimal oldPayments oldPayments-nonnegative further further₊
    (λ state member client → isTrans≡≤ᵣ _ _ _ (sym (funExt⁻ (trade-claims-agree state) client))
      (coverage state member client)))

requested-payments-ready :
  brokerReady (MarginWorkflow.afterRequests oldPayments)
    (MarginWorkflow.afterRequests-nonnegative oldPayments oldPayments-nonnegative) liquidity100 ≡ true
requested-payments-ready = refl

-- The full combined call is present, but incorrectly credited entirely to A.
misallocatedPayments : MarginWorkflow.Payments
misallocatedPayments = two [ 233 / 5 ] 0

misallocated-nonnegative : MarginWorkflow.NonnegativePayments misallocatedPayments
misallocated-nonnegative F.zero = ℚ.decℚ≤?
misallocated-nonnegative (F.suc F.zero) = ℚ.decℚ≤?

same-total-cash : sum (λ client → rat (misallocatedPayments client))
  ≡ sum (λ client → rat (fullPayments client))
same-total-cash = ℝ!

misallocated-cash-refused : brokerReady misallocatedPayments misallocated-nonnegative liquidity100 ≡ false
misallocated-cash-refused = refl

-- Equal base value at reference FX does not supply the foreign currency.
domesticOnly : Liquidity
domesticOnly = two 200 0

same-base-funding-value : dot Operations.baseFX (λ currency → rat (domesticOnly currency))
  ≡ dot Operations.baseFX (λ currency → rat (liquidity100 currency))
same-base-funding-value = ℝ!

wrong-currency-funding-refused :
  brokerReady fullPayments fullPayments-nonnegative domesticOnly ≡ false
wrong-currency-funding-refused = refl

-- An arbitrary number of actual receipts is processed separately for each
-- client. The valuation functions and admissible quote box stay fixed.
ClientHistories : Type₀
ClientHistories = Fin 2 → History.PaymentHistory

receivedTotals : ClientHistories → MarginWorkflow.Payments
receivedTotals histories client = History.totalReceived (histories client)

receivedTotals-nonnegative : ∀ histories → MarginWorkflow.NonnegativePayments (receivedTotals histories)
receivedTotals-nonnegative histories client = History.totalReceived-nonnegative (histories client)

historyCollateral : ClientHistories → FXState → Vector 2
historyCollateral histories state client =
  History.creditHistory (λ valuation → collateral valuation client) (histories client) state

history-collateral-agrees : ∀ histories →
  historyCollateral histories ≡ MarginWorkflow.postedCollateral (receivedTotals histories)
history-collateral-agrees histories = funExt λ state → funExt λ client →
  funExt⁻ (History.creditHistory-total (λ valuation → collateral valuation client) (histories client)) state

historyReady : ClientHistories → Liquidity → Bool
historyReady histories = brokerReady (receivedTotals histories) (receivedTotals-nonnegative histories)

-- Transport the global certificate to the collateral produced by the
-- actual sequential receipt fold, uniformly over every quote in the box.
history-end-to-end : ∀ histories liquidity → historyReady histories liquidity ≡ true →
  BookGuarantee (historyCollateral histories) liquidity
history-end-to-end histories liquidity proof =
  subst (λ C → BookGuarantee C liquidity) (sym (history-collateral-agrees histories))
    (broker-end-to-end (receivedTotals histories) (receivedTotals-nonnegative histories) liquidity proof)

private
  receivedPayments : ClientHistories → Σ MarginWorkflow.Payments MarginWorkflow.NonnegativePayments
  receivedPayments histories = receivedTotals histories , receivedTotals-nonnegative histories

  received-payments-same : ∀ first second →
    (∀ client → History.totalReceived (first client) ≡ History.totalReceived (second client)) →
    receivedPayments first ≡ receivedPayments second
  received-payments-same first second totals =
    Σ≡Prop (λ paid → isPropΠ (λ client → ℚ.isProp≤ 0 (paid client))) (funExt totals)

-- Equal per-client totals preserve the complete broker decision, including
-- the independent funding check. Unequal client totals cannot be exchanged.
history-batching-invariant : ∀ first second →
  (∀ client → History.totalReceived (first client) ≡ History.totalReceived (second client)) →
  ∀ liquidity → historyReady first liquidity ≡ historyReady second liquidity
history-batching-invariant first second totals liquidity =
  cong (λ paid → brokerReady (fst paid) (snd paid) liquidity)
    (received-payments-same first second totals)

clientClaimProfiles clientCollateralProfiles : Fin 2 → Vector 2
clientClaimProfiles = two Joint.jointClaimA Joint.jointClaimB
clientCollateralProfiles = two Joint.jointCollateralA Joint.jointCollateralB

clientReports : ∀ client → Control.ExactMargin (clientClaimProfiles client) (clientCollateralProfiles client)
clientReports F.zero = Joint.jointReportA
clientReports (F.suc F.zero) = Joint.jointReportB

-- The existing iterative report processor agrees with the requests used
-- by the universal-domain workflow, for every finite receipt history.
history-reports-agree : ∀ histories client →
  Control.amount (History.processHistory (clientReports client) (histories client))
    ≡ MarginWorkflow.outstanding (receivedTotals histories) client
history-reports-agree histories F.zero =
  History.processHistory-outstanding Joint.jointReportA (histories F.zero)
history-reports-agree histories (F.suc F.zero) =
  History.processHistory-outstanding Joint.jointReportB (histories (F.suc F.zero))

-- The old single-factor calls were already received. Two further receipts
-- complete the new joint-box requests: A pays 10 and B pays 8.
stagedReceipts : ClientHistories
stagedReceipts F.zero = History.receipt 15 ℚ.decℚ≤? ∷ History.receipt 10 ℚ.decℚ≤? ∷ []
stagedReceipts (F.suc F.zero) =
  History.receipt [ 68 / 5 ] ℚ.decℚ≤? ∷ History.receipt 8 ℚ.decℚ≤? ∷ []

staged-receipts-ready : historyReady stagedReceipts liquidity100 ≡ true
staged-receipts-ready = refl

staged-broker-guarantee : BookGuarantee (historyCollateral stagedReceipts) liquidity100
staged-broker-guarantee = history-end-to-end stagedReceipts liquidity100 staged-receipts-ready
