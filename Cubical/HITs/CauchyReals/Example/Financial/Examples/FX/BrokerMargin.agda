-- FX cashflows, collateral haircuts and client netting are motivated by
-- ../../REFERENCES.md#bis-fx-2016, #bcbs-iosco-margin-2020 and
-- #bcbs-settlement-2013. Spot shocks of +/-20%, discount factor 0.9 and
-- the 20% haircut are synthetic; the resulting calls are not regulatory
-- requirements. The cited margin framework excludes physically settled FX
-- forwards/swaps from its general requirements; see #bcbs-iosco-margin-2020.

module Cubical.HITs.CauchyReals.Example.Financial.Examples.FX.BrokerMargin where

open import Cubical.HITs.CauchyReals.Example.Financial.Core.Vectors public using (two)

open import Cubical.HITs.CauchyReals.Example.Financial.Instruments.FXSwap
open import Cubical.HITs.CauchyReals.Example.Financial.Margin.Base
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.Shortfall
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.WorstCase
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.ExpectedShortfall
open import Cubical.HITs.CauchyReals.Foundation.Rationals using ([_/_])
open import Cubical.Data.NatPlusOne using (fromNatℕ₊₁)
open import Cubical.Data.Int.Base using (fromNatℤ)
open import Cubical.Data.Empty using (⊥)
open import Cubical.HITs.CauchyReals.Algebra.Order.Properties using (isIrrefl<ᵣ)
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
import Cubical.Data.FinData.Base as F
import Cubical.Data.Nat.Order as N
import Cubical.HITs.CauchyReals.Example.Financial.Margin.ClientNetting as C
import Cubical.HITs.CauchyReals.Example.Financial.Examples.CommonScenarioData as Scenario

-- Two principal-only swaps share dates 0 and 30. Rates 1/1 describe the
-- zero-swap-points reference case; the instrument theory permits any
-- positive near/far rates. These are abstract currency units, not live data.
swap60 swap40 : FXSwap
swap60 = fx-swap 60 1 1 decℚ<ᵣ? decℚ<ᵣ? 0 30 N.zero-<-suc
swap40 = fx-swap 40 1 1 decℚ<ᵣ? decℚ<ᵣ? 0 30 N.zero-<-suc

swaps : Fin 2 → FXSwap
swaps F.zero = swap60
swaps (F.suc F.zero) = swap40

reference : FXState
reference = fx-state 1 1 1 decℚ<ᵣ? decℚ<ᵣ? decℚ<ᵣ?

-- Scenario 0: foreign appreciates. 1: foreign depreciates.
-- 2: domestic discount factor falls. 3: effective foreign factor falls.
-- No assertion of calibrated scenario probabilities or curve dynamics.
states : Fin 2 → Fin 4 → FXState
states trade F.zero = fx-state (rat [ 6 / 5 ]) 1 1 decℚ<ᵣ? decℚ<ᵣ? decℚ<ᵣ?
states trade (F.suc F.zero) = fx-state (rat [ 4 / 5 ]) 1 1 decℚ<ᵣ? decℚ<ᵣ? decℚ<ᵣ?
states trade (F.suc (F.suc F.zero)) = fx-state 1 (rat [ 9 / 10 ]) 1 decℚ<ᵣ? decℚ<ᵣ? decℚ<ᵣ?
states trade (F.suc (F.suc (F.suc F.zero))) = fx-state 1 1 (rat [ 9 / 10 ]) decℚ<ᵣ? decℚ<ᵣ? decℚ<ᵣ?

holdingsA holdingsB : Vector 2
holdingsA = two 1 1
holdingsB = two -1 -1

claimA claimB : Vector 4
claimA = clientClaim swaps states holdingsA
claimB = clientClaim swaps states holdingsB

claimA-values : claimA ≡ Scenario.four 20 -20 10 -10
claimA-values = funExt λ
  { F.zero → ℝ!
  ; (F.suc F.zero) → ℝ!
  ; (F.suc (F.suc F.zero)) → ℝ!
  ; (F.suc (F.suc (F.suc F.zero))) → ℝ!
  }

claimB-values : claimB ≡ Scenario.four -20 20 -10 10
claimB-values = funExt λ
  { F.zero → ℝ!
  ; (F.suc F.zero) → ℝ!
  ; (F.suc (F.suc F.zero)) → ℝ!
  ; (F.suc (F.suc (F.suc F.zero))) → ℝ!
  }

market-neutral : ∀ i → claimA i +ᵣ claimB i ≡ 0
market-neutral i = ℝ!

initial-marks-zero : ∀ j → farValue (swaps j) reference ≡ 0
initial-marks-zero F.zero = ℝ!
initial-marks-zero (F.suc F.zero) = ℝ!

spots : Vector 4
spots i = spot (states F.zero i)

-- Client A posts 5 domestic. B posts 10 foreign; 80% of its scenario
-- conversion value is eligible. Client B's exposure rises when this
-- collateral loses domestic value, so freezing spot would under-margin it.
collateralA collateralB : Vector 4
collateralA i = 5
collateralB = currencyCollateral 0 (rat [ 4 / 5 ]) spots 10

collateralB-values : collateralB ≡ Scenario.four (rat [ 48 / 5 ]) (rat [ 32 / 5 ]) 8 8
collateralB-values = funExt λ
  { F.zero → ℝ!
  ; (F.suc F.zero) → ℝ!
  ; (F.suc (F.suc F.zero)) → ℝ!
  ; (F.suc (F.suc (F.suc F.zero))) → ℝ!
  }

collateralA-nonnegative : ∀ i → 0 ≤ᵣ collateralA i
collateralA-nonnegative i = decℚ≤ᵣ?

collateralB-nonnegative : ∀ i → 0 ≤ᵣ collateralB i
collateralB-nonnegative = currencyCollateral-nonnegative 0 (rat [ 4 / 5 ]) spots 10
  decℚ≤ᵣ? decℚ≤ᵣ? (λ i → <ᵣWeaken≤ᵣ 0 (spots i) (spot-positive (states F.zero i))) decℚ≤ᵣ?

private
  stop-positive : ∀ x c r → x -ᵣ c ≡ r → 0 ≤ᵣ r → stopLoss x c ≡ r
  stop-positive = stopLoss-evaluate

residualA residualB : Vector 4
residualA i = stopLoss (claimA i) (collateralA i)
residualB i = stopLoss (claimB i) (collateralB i)

residualA-values : residualA ≡ Scenario.four 15 0 5 0
residualA-values = funExt λ i → cong (λ x → stopLoss x 5) (funExt⁻ claimA-values i) ∙ evaluate i
  where
  evaluate : ∀ i → stopLoss (Scenario.four 20 -20 10 -10 i) 5 ≡ Scenario.four 15 0 5 0 i
  evaluate F.zero = stop-positive 20 5 15 ℝ! decℚ≤ᵣ?
  evaluate (F.suc F.zero) = stopLoss-zero-below -20 5 decℚ≤ᵣ?
  evaluate (F.suc (F.suc F.zero)) = stop-positive 10 5 5 ℝ! decℚ≤ᵣ?
  evaluate (F.suc (F.suc (F.suc F.zero))) = stopLoss-zero-below -10 5 decℚ≤ᵣ?

residualB-values : residualB ≡ Scenario.four 0 (rat [ 68 / 5 ]) 0 2
residualB-values = funExt λ i → cong₂ stopLoss (funExt⁻ claimB-values i)
  (funExt⁻ collateralB-values i) ∙ evaluate i
  where
  evaluate : ∀ i → stopLoss (Scenario.four -20 20 -10 10 i)
    (Scenario.four (rat [ 48 / 5 ]) (rat [ 32 / 5 ]) 8 8 i) ≡ Scenario.four 0 (rat [ 68 / 5 ]) 0 2 i
  evaluate F.zero = stopLoss-zero-below -20 (rat [ 48 / 5 ]) decℚ≤ᵣ?
  evaluate (F.suc F.zero) = stop-positive 20 (rat [ 32 / 5 ]) (rat [ 68 / 5 ]) ℝ! decℚ≤ᵣ?
  evaluate (F.suc (F.suc F.zero)) = stopLoss-zero-below -10 8 decℚ≤ᵣ?
  evaluate (F.suc (F.suc (F.suc F.zero))) = stop-positive 10 8 2 ℝ! decℚ≤ᵣ?

callA-exact : requiredMargin claimA collateralA ≡ 15
callA-exact = cong worstCase residualA-values ∙ isAntisym≤ᵣ _ _
  (worstCase-least (Scenario.four 15 0 5 0) 15 bound) (worstCase-upper (Scenario.four 15 0 5 0) F.zero)
  where
  bound : ∀ i → Scenario.four 15 0 5 0 i ≤ᵣ 15
  bound F.zero = decℚ≤ᵣ?
  bound (F.suc F.zero) = decℚ≤ᵣ?
  bound (F.suc (F.suc F.zero)) = decℚ≤ᵣ?
  bound (F.suc (F.suc (F.suc F.zero))) = decℚ≤ᵣ?

callB-exact : requiredMargin claimB collateralB ≡ rat [ 68 / 5 ]
callB-exact = cong worstCase residualB-values ∙ isAntisym≤ᵣ _ _
  (worstCase-least (Scenario.four 0 (rat [ 68 / 5 ]) 0 2) (rat [ 68 / 5 ]) bound)
  (worstCase-upper (Scenario.four 0 (rat [ 68 / 5 ]) 0 2) (F.suc F.zero))
  where
  bound : ∀ i → Scenario.four 0 (rat [ 68 / 5 ]) 0 2 i ≤ᵣ rat [ 68 / 5 ]
  bound F.zero = decℚ≤ᵣ?
  bound (F.suc F.zero) = decℚ≤ᵣ?
  bound (F.suc (F.suc F.zero)) = decℚ≤ᵣ?
  bound (F.suc (F.suc (F.suc F.zero))) = decℚ≤ᵣ?

-- Each client's own collateral must cover its own worst scenario. Those
-- scenarios need not coincide, so the sum of calls is a separate quantity
-- from the broker's worst aggregate residual-exposure diagnostic below.
total-client-calls : requiredMargin claimA collateralA +ᵣ requiredMargin claimB collateralB
  ≡ rat [ 143 / 5 ]
total-client-calls = cong₂ _+ᵣ_ callA-exact callB-exact ∙ ℝ!

claims collateral : Fin 4 → Vector 2
claims i = two (claimA i) (claimB i)
collateral i = two (collateralA i) (collateralB i)

brokerExposure : Vector 4
brokerExposure i = C.brokerResidual (claims i) (collateral i)

broker-exposure-values : brokerExposure ≡ Scenario.four 15 (rat [ 68 / 5 ]) 5 2
broker-exposure-values = cong₂ (λ (X Y : Vector 4) (i : Fin 4) → X i +ᵣ (Y i +ᵣ 0))
  residualA-values residualB-values
  ∙ funExt λ
    { F.zero → ℝ!
    ; (F.suc F.zero) → ℝ!
    ; (F.suc (F.suc F.zero)) → ℝ!
    ; (F.suc (F.suc (F.suc F.zero))) → ℝ!
    }

broker-stress : worstCase brokerExposure ≡ 15
broker-stress = cong worstCase broker-exposure-values ∙ isAntisym≤ᵣ _ _
  (worstCase-least (Scenario.four 15 (rat [ 68 / 5 ]) 5 2) 15 bound)
  (worstCase-upper (Scenario.four 15 (rat [ 68 / 5 ]) 5 2) F.zero)
  where
  bound : ∀ i → Scenario.four 15 (rat [ 68 / 5 ]) 5 2 i ≤ᵣ 15
  bound F.zero = decℚ≤ᵣ?
  bound (F.suc F.zero) = decℚ≤ᵣ?
  bound (F.suc (F.suc F.zero)) = decℚ≤ᵣ?
  bound (F.suc (F.suc (F.suc F.zero))) = decℚ≤ᵣ?

-- Counterparty risk is evaluated on separate positive claims. Pooling
-- signed client marks here would incorrectly report no residual at all.
pooled-exposure-zero : ∀ i → C.pooledResidual (claims i) (collateral i) ≡ 0
pooled-exposure-zero i = stopLoss-zero-below _ _
  (isTrans≡≤ᵣ _ _ _ claim-zero (sum-nonnegative (collateral i) positive))
  where
  claim-zero : sum (claims i) ≡ 0
  claim-zero = ℝ!
  positive : ∀ j → 0 ≤ᵣ collateral i j
  positive F.zero = collateralA-nonnegative i
  positive (F.suc F.zero) = collateralB-nonnegative i

-- FX conversion of collateral must be stressed together with the claim.
-- Freezing B's collateral at its current eligible value 8 gives call 12.
frozenCollateralB : Vector 4
frozenCollateralB i = 8

frozen-callB : requiredMargin claimB frozenCollateralB ≡ 12
frozen-callB = cong worstCase (funExt evaluate) ∙ isAntisym≤ᵣ _ _
  (worstCase-least (Scenario.four 0 12 0 2) 12 bound) (worstCase-upper (Scenario.four 0 12 0 2) (F.suc F.zero))
  where
  stops : ∀ i → stopLoss (Scenario.four -20 20 -10 10 i) 8 ≡ Scenario.four 0 12 0 2 i
  stops F.zero = stopLoss-zero-below -20 8 decℚ≤ᵣ?
  stops (F.suc F.zero) = stop-positive 20 8 12 ℝ! decℚ≤ᵣ?
  stops (F.suc (F.suc F.zero)) = stopLoss-zero-below -10 8 decℚ≤ᵣ?
  stops (F.suc (F.suc (F.suc F.zero))) = stop-positive 10 8 2 ℝ! decℚ≤ᵣ?
  evaluate : ∀ i → stopLoss (claimB i) 8 ≡ Scenario.four 0 12 0 2 i
  evaluate i = cong (λ x → stopLoss x 8) (funExt⁻ claimB-values i) ∙ stops i
  bound : ∀ i → Scenario.four 0 12 0 2 i ≤ᵣ 12
  bound F.zero = decℚ≤ᵣ?
  bound (F.suc F.zero) = decℚ≤ᵣ?
  bound (F.suc (F.suc F.zero)) = decℚ≤ᵣ?
  bound (F.suc (F.suc (F.suc F.zero))) = decℚ≤ᵣ?

frozen-call-insufficient : requiredMargin claimB collateralB ≤ᵣ 12 → ⊥
frozen-call-insufficient bound = isIrrefl<ᵣ 12
  (isTrans<≤ᵣ _ _ _ decℚ<ᵣ? (isTrans≡≤ᵣ _ _ _ (sym callB-exact) bound))

remaining-FX-shortfall : stopLoss (claimB (F.suc F.zero))
  (postCash collateralB 12 (F.suc F.zero)) ≡ rat [ 8 / 5 ]
remaining-FX-shortfall = cong₂ stopLoss (funExt⁻ claimB-values (F.suc F.zero))
  (cong (_+ᵣ 12) (funExt⁻ collateralB-values (F.suc F.zero)))
  ∙ stop-positive 20 (rat [ 32 / 5 ] +ᵣ 12) (rat [ 8 / 5 ]) ℝ! decℚ≤ᵣ?

paidA-zero : requiredMargin claimA (postCash collateralA 15) ≡ 0
paidA-zero = sufficient-cash-zero claimA collateralA 15 (≡ᵣWeaken≤ᵣ _ _ callA-exact)

paidB-zero : requiredMargin claimB (postCash collateralB (rat [ 68 / 5 ])) ≡ 0
paidB-zero = sufficient-cash-zero claimB collateralB (rat [ 68 / 5 ]) (≡ᵣWeaken≤ᵣ _ _ callB-exact)

-- Optional distributional diagnostic of the residual EXPOSURE profile.
-- These are illustrative scenario weights, not estimated default probabilities.
module Tail = TailRisk Scenario.equalProbability Scenario.halfTail

broker-mean-exposure : expectation Scenario.equalProbability brokerExposure ≡ rat [ 89 / 10 ]
broker-mean-exposure = cong (expectation Scenario.equalProbability) broker-exposure-values ∙ ℝ!

broker-tail-objective : Tail.objective brokerExposure 5 ≡ rat [ 143 / 10 ]
broker-tail-objective = cong (λ X → Tail.objective X 5) broker-exposure-values
  ∙ cong (λ X → 5 +ᵣ 2 ·ᵣ expectation Scenario.equalProbability X) (funExt stops) ∙ ℝ!
  where
  stops : ∀ i → stopLoss (Scenario.four 15 (rat [ 68 / 5 ]) 5 2 i) 5
    ≡ Scenario.four 10 (rat [ 43 / 5 ]) 0 0 i
  stops F.zero = stop-positive 15 5 10 ℝ! decℚ≤ᵣ?
  stops (F.suc F.zero) = stop-positive (rat [ 68 / 5 ]) 5 (rat [ 43 / 5 ]) ℝ! decℚ≤ᵣ?
  stops (F.suc (F.suc F.zero)) = stopLoss-zero-below 5 5 decℚ≤ᵣ?
  stops (F.suc (F.suc (F.suc F.zero))) = stopLoss-zero-below 2 5 decℚ≤ᵣ?

broker-dual-value : expectation Scenario.stress01 brokerExposure ≡ rat [ 143 / 10 ]
broker-dual-value = cong (expectation Scenario.stress01) broker-exposure-values ∙ ℝ!

broker-tail-certificate : Tail.OptimalityCertificate brokerExposure
broker-tail-certificate .Tail.threshold = 5
broker-tail-certificate .Tail.dual = Scenario.stress01
broker-tail-certificate .Tail.dual-admissible = Scenario.stress01-admissible
broker-tail-certificate .Tail.tight = broker-tail-objective ∙ sym broker-dual-value

broker-CVaR : Tail.IsCVaR brokerExposure (rat [ 143 / 10 ])
broker-CVaR = subst (Tail.IsCVaR brokerExposure) broker-tail-objective
  (Tail.certified-CVaR brokerExposure broker-tail-certificate)
