-- Client close-out exposure, payment obligations and currency funding must be
-- distinguished as in ../../REFERENCES.md#bcbs-settlement-2013.
-- The broker book is synthetic; available collateral and loss severity are
-- supplied inputs. Posting close-out margin does not by itself establish
-- payment-netting rights or provide the currencies needed for settlement.

module Cubical.HITs.CauchyReals.Example.Financial.Examples.FX.BrokerOperations where

open import Cubical.HITs.CauchyReals.Example.Financial.Margin.MarginControl
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.Shortfall
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.WorstCase
open import Cubical.HITs.CauchyReals.Foundation.Rationals using ([_/_]; module ℚ; ℚ!)
open import Cubical.Data.NatPlusOne using (fromNatℕ₊₁)
open import Cubical.Data.Int.Base using (fromNatℤ)
open import Cubical.Data.Empty using (⊥)
open import Cubical.HITs.CauchyReals.Algebra.Order.Properties using (isIrrefl<ᵣ)
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
import Cubical.HITs.CauchyReals.Example.Financial.Examples.FX.BrokerMargin as B
import Cubical.HITs.CauchyReals.Example.Financial.Instruments.FXSwap as FX
import Cubical.HITs.CauchyReals.Example.Financial.Margin.ClientNetting as Clients
import Cubical.HITs.CauchyReals.Example.Financial.Margin.CounterpartyRisk as Credit
import Cubical.HITs.CauchyReals.Example.Financial.Settlement.Base as Settlement
import Cubical.HITs.CauchyReals.Example.Financial.Examples.CommonScenarioData as Scenario
import Cubical.Data.FinData.Base as F
import Cubical.HITs.PropositionalTruncation as PT

-- Operational reports preserve the client netting-set identity and are
-- certified against the stressed, currency-sensitive collateral model.
reportA : ExactMargin B.claimA B.collateralA
reportA .amount = 15
reportA .exact = B.callA-exact

reportB : ExactMargin B.claimB B.collateralB
reportB .amount = [ 68 / 5 ]
reportB .exact = B.callB-exact

clientA-paid-fifteen : payment-status (checkPayment reportA 15 ℚ.decℚ≤?) ≡ covered
clientA-paid-fifteen = refl

clientA-paid-fourteen : payment-status (checkPayment reportA 14 ℚ.decℚ≤?) ≡ more-due
clientA-paid-fourteen = refl

clientB-paid-twelve : payment-status (checkPayment reportB 12 ℚ.decℚ≤?) ≡ more-due
clientB-paid-twelve = refl

clientB-outstanding : outstandingRequest reportB 12 ≡ [ 8 / 5 ]
clientB-outstanding = ℚ.maxComm ([ 68 / 5 ] ℚ.- 12) 0
  ∙ ℚ.≤→max 0 ([ 68 / 5 ] ℚ.- 12) ℚ.decℚ≤? ∙ ℚ!

clientB-paid-full : payment-status (checkPayment reportB [ 68 / 5 ] ℚ.decℚ≤?) ≡ covered
clientB-paid-full = refl

reportB-after-twelve : ExactMargin B.claimB (postCash B.collateralB 12)
reportB-after-twelve = recordPayment reportB 12 ℚ.decℚ≤?

clientB-second-payment :
  payment-status (checkPayment reportB-after-twelve [ 8 / 5 ] ℚ.decℚ≤?) ≡ covered
clientB-second-payment = refl

clientB-partial-residual : requiredMargin B.claimB (postCash B.collateralB 12) ≡ rat [ 8 / 5 ]
clientB-partial-residual = exact reportB-after-twelve ∙ cong rat clientB-outstanding

clientB-two-payments-clear :
  requiredMargin B.claimB (postCash (postCash B.collateralB 12) (rat [ 8 / 5 ])) ≡ 0
clientB-two-payments-clear =
  cong (λ q → requiredMargin B.claimB (postCash (postCash B.collateralB 12) (rat q)))
    (sym clientB-outstanding)
  ∙ request-paid-zero reportB 12

-- These are collateral states AFTER each client's cash is actually paid
-- and available for its own closeout. No surplus is reassigned to a client.
paidCollateral : Fin 4 → Vector 2
paidCollateral i = B.two (postCash B.collateralA 15 i)
  (postCash B.collateralB (rat [ 68 / 5 ]) i)

paid-coverage : ∀ i client → B.claims i client ≤ᵣ paidCollateral i client
paid-coverage i F.zero = margin-bound→coverage B.claimA B.collateralA 15
  (≡ᵣWeaken≤ᵣ _ _ B.callA-exact) i
paid-coverage i (F.suc F.zero) = margin-bound→coverage B.claimB B.collateralB (rat [ 68 / 5 ])
  (≡ᵣWeaken≤ᵣ _ _ B.callB-exact) i

all-paid-broker-residual-zero : ∀ i → Clients.brokerResidual (B.claims i) (paidCollateral i) ≡ 0
all-paid-broker-residual-zero i = sum-cong _ (λ _ → 0)
  (λ client → stopLoss-zero-below (B.claims i client) (paidCollateral i client) (paid-coverage i client))
  ∙ sum-zero 2

-- Severity includes default occurrence and unrecovered fraction. It may
-- depend on both scenario and client; no independence assumption is used.
initial-closeout-loss-bound : ∀ (θ : Fin 4 → Credit.Severity 2) i →
  Credit.scenarioLoss B.claims B.collateral θ i ≤ᵣ B.brokerExposure i
initial-closeout-loss-bound θ = Credit.scenario-loss≤exposure B.claims B.collateral θ

initial-closeout-stress-bound : ∀ (θ : Fin 4 → Credit.Severity 2) →
  worstCase (Credit.scenarioLoss B.claims B.collateral θ) ≤ᵣ 15
initial-closeout-stress-bound θ = isTrans≤≡ᵣ _ _ _
  (Credit.worstCase-loss≤exposure B.claims B.collateral θ) B.broker-stress

module CreditTail = Credit.ScenarioRisk Scenario.equalProbability Scenario.halfTail B.claims B.collateral

initial-closeout-tail-budget : ∀ (θ : Fin 4 → Credit.Severity 2) →
  B.Tail.Accepted (Credit.scenarioLoss B.claims B.collateral θ) (rat [ 143 / 10 ])
initial-closeout-tail-budget = CreditTail.exposure-budget→loss-budget (rat [ 143 / 10 ])
  PT.∣ 5 , ≡ᵣWeaken≤ᵣ _ _ B.broker-tail-objective ∣₁

all-paid-closeout-loss-zero : ∀ (θ : Fin 4 → Credit.Severity 2) i →
  Credit.scenarioLoss B.claims paidCollateral θ i ≡ 0
all-paid-closeout-loss-zero θ i =
  Credit.covered-loss-zero (B.claims i) (paidCollateral i) (θ i) (paid-coverage i)

-- The actual four far-leg payment instructions: two swaps for A and the
-- reversed swaps for B. All occur at date30, but remain separate trades.
farTrades : Fin 4 → FX.FXSwap
farTrades F.zero = B.swap60
farTrades (F.suc F.zero) = B.swap40
farTrades (F.suc (F.suc F.zero)) = FX.reverseSwap B.swap60
farTrades (F.suc (F.suc (F.suc F.zero))) = FX.reverseSwap B.swap40

farBook : Settlement.Book 4 2
farBook trade = FX.cashflow (farTrades trade) FX.far

same-far-date : ∀ trade → FX.settlementDate (farTrades trade) FX.far ≡ 30
same-far-date F.zero = refl
same-far-date (F.suc F.zero) = refl
same-far-date (F.suc (F.suc F.zero)) = refl
same-far-date (F.suc (F.suc (F.suc F.zero))) = refl

far-net-zero : Settlement.netFlow farBook ≡ (λ _ → 0)
far-net-zero = funExt λ { F.zero → ℝ! ; (F.suc F.zero) → ℝ! }

private
  payments : Settlement.Book 4 2
  payments F.zero = B.two 60 0
  payments (F.suc F.zero) = B.two 40 0
  payments (F.suc (F.suc F.zero)) = B.two 0 60
  payments (F.suc (F.suc (F.suc F.zero))) = B.two 0 40

  positive-outgoing : ∀ x y → -ᵣ x ≡ y → 0 ≤ᵣ y → positivePart (-ᵣ x) ≡ y
  positive-outgoing x y equation y₊ = cong positivePart equation ∙ positivePart-of-nonnegative y y₊

  zero-outgoing : ∀ x y → -ᵣ x ≡ y → y ≤ᵣ 0 → positivePart (-ᵣ x) ≡ 0
  zero-outgoing x y equation y≤zero = cong positivePart equation ∙ positivePart-of-nonpositive y y≤zero

  outgoing-values : ∀ trade c → Settlement.outgoing (farBook trade) c ≡ payments trade c
  outgoing-values F.zero F.zero = positive-outgoing _ 60 ℝ! decℚ≤ᵣ?
  outgoing-values F.zero (F.suc F.zero) = zero-outgoing _ -60 ℝ! decℚ≤ᵣ?
  outgoing-values (F.suc F.zero) F.zero = positive-outgoing _ 40 ℝ! decℚ≤ᵣ?
  outgoing-values (F.suc F.zero) (F.suc F.zero) = zero-outgoing _ -40 ℝ! decℚ≤ᵣ?
  outgoing-values (F.suc (F.suc F.zero)) F.zero = zero-outgoing _ -60 ℝ! decℚ≤ᵣ?
  outgoing-values (F.suc (F.suc F.zero)) (F.suc F.zero) = positive-outgoing _ 60 ℝ! decℚ≤ᵣ?
  outgoing-values (F.suc (F.suc (F.suc F.zero))) F.zero = zero-outgoing _ -40 ℝ! decℚ≤ᵣ?
  outgoing-values (F.suc (F.suc (F.suc F.zero))) (F.suc F.zero) = positive-outgoing _ 40 ℝ! decℚ≤ᵣ?

far-gross-outgoing : Settlement.grossOutgoing farBook ≡ B.two 100 100
far-gross-outgoing = funExt λ c →
  sum-cong (λ trade → Settlement.outgoing (farBook trade) c) (λ trade → payments trade c)
    (λ trade → outgoing-values trade c)
  ∙ total c
  where
  total : ∀ c → sum (λ trade → payments trade c) ≡ B.two 100 100 c
  total F.zero = ℝ!
  total (F.suc F.zero) = ℝ!

fundingBuffers : Settlement.Cashflow 2
fundingBuffers = B.two 100 100

funded-gross-in-both-currencies : Settlement.GrossFundingCertificate farBook fundingBuffers
funded-gross-in-both-currencies c = ≡ᵣWeaken≤ᵣ _ _ (funExt⁻ far-gross-outgoing c)

baseFX : Vector 2
baseFX = B.two 1 1

gross-base-two-hundred : dot baseFX (Settlement.grossOutgoing farBook) ≡ 200
gross-base-two-hundred = cong (dot baseFX) far-gross-outgoing ∙ ℝ!

zero-net-base-mark : Settlement.baseMark baseFX (Settlement.netFlow farBook) ≡ 0
zero-net-base-mark = cong (dot baseFX) far-net-zero ∙ ℝ!

-- Even after closeout margin is fully paid, these gross principal payment
-- instructions remain. The client collateral is not declared reusable for
-- settlement funding, and no cross-client payment-netting right is assumed.
gross-funding-cannot-be-zero : Settlement.GrossFundingCertificate farBook (λ _ → 0) → ⊥
gross-funding-cannot-be-zero zero-funded = isIrrefl<ᵣ 0
  (isTrans<≤ᵣ 0 100 0 decℚ<ᵣ?
    (isTrans≡≤ᵣ _ _ _ (sym (funExt⁻ far-gross-outgoing F.zero)) (zero-funded F.zero)))
