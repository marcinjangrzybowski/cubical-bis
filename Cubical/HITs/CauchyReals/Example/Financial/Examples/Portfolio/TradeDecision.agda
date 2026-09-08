-- This executable fee-regime decision instantiates proportional-cost CVaR
-- optimization: ../../REFERENCES.md#boyd-2017 and #rockafellar-uryasev-2002.
-- The rational fee comparisons and exact threshold 4 belong to the synthetic
-- four-scenario market; they are not calibrated trading recommendations.

module Cubical.HITs.CauchyReals.Example.Financial.Examples.Portfolio.TradeDecision where

open import Cubical.HITs.CauchyReals.Example.Financial.Portfolio.Base
open import Cubical.HITs.CauchyReals.Example.Financial.Examples.Portfolio.Rebalancing
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.RiskControl using (Decision; pass; fail)
open import Cubical.HITs.CauchyReals.Foundation.Rationals using (ℚ; module ℚ; [_/_]; fromNatℚ)
open import Cubical.Data.NatPlusOne using (fromNatℕ₊₁)
open import Cubical.Data.Int.Base using (fromNatℤ)
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Relation.Nullary using (Dec; yes; no)
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
import Cubical.HITs.CauchyReals.Example.Financial.Examples.Portfolio.Diversification as D
import Cubical.Data.FinData.Base as F

-- A trading decision contains the allocation and a proof of its global
-- optimality for net CVaR in this particular two-asset, four-scenario market.
-- Its competitors include all signed real holdings with total weight one.
record CertifiedTrade (s : ℝ) : Type₀ where
  constructor certified-trade
  field
    chosenWeight : ℝ
    long-only : (0 ≤ᵣ chosenWeight) × (chosenWeight ≤ᵣ 1)
    riskValue : ℝ
    CVaR-value : Risk.IsCVaR (netLoss s chosenWeight) riskValue
    global-bound : ∀ w t → riskValue ≤ᵣ Risk.objective (netLoss s w) t
open CertifiedTrade public

-- Fees, unlike arbitrary real market data, are rational inputs to this
-- executable rule. The boundary s=4 selects the 3/4 allocation among ties.
chooseTrade : (s : ℚ) → 0 ℚ.≤ s → CertifiedTrade (rat s)
chooseTrade s s₊ with ℚ.≤Dec s 4
... | yes s≤4 = certified-trade target (decℚ≤ᵣ? , decℚ≤ᵣ?)
  (2 +ᵣ rat s ·ᵣ D.quarter) (target-net-CVaR (rat s))
  (low-fee-global-bound (rat s) (≤ℚ→≤ᵣ 0 s s₊) (≤ℚ→≤ᵣ s 4 s≤4))
... | no s≰4 = certified-trade 1 (decℚ≤ᵣ? , decℚ≤ᵣ?) 3
  (no-trade-CVaR (rat s))
  (high-fee-global-bound (rat s)
    (≤ℚ→≤ᵣ 4 s (ℚ.≮→≥ s 4 (λ s<4 → s≰4 (ℚ.<Weaken≤ s 4 s<4)))))

-- A consumer receives the ordinary Allocation type used by portfolio and
-- policy operations, including all normalization and nonnegativity proofs.
chosenAllocation : ∀ s → CertifiedTrade s → Allocation 2
chosenAllocation s trade = holdings (chosenWeight trade) , nonnegative ,
  holdings-total (chosenWeight trade)
  where
  nonnegative : ∀ i → 0 ≤ᵣ holdings (chosenWeight trade) i
  nonnegative F.zero = fst (long-only trade)
  nonnegative (F.suc F.zero) =
    complement-nonnegative (chosenWeight trade , long-only trade)

chosen-allocation-loss : ∀ s (trade : CertifiedTrade s) →
  portfolioLoss market (probability (chosenAllocation s trade)) ≡ D.mixed (chosenWeight trade)
chosen-allocation-loss s trade = holdings-loss (chosenWeight trade)

-- These choices compute by rational comparison. The exact arithmetic on
-- the resulting Cauchy-real risk values is separately certified by ℝ!.
fee-one-trades : chosenWeight (chooseTrade 1 ℚ.decℚ≤?) ≡ target
fee-one-trades = refl

fee-one-risk : riskValue (chooseTrade 1 ℚ.decℚ≤?) ≡ rat [ 9 / 4 ]
fee-one-risk = ℝ!

fee-five-holds : chosenWeight (chooseTrade 5 ℚ.decℚ≤?) ≡ 1
fee-five-holds = refl

fee-five-risk : riskValue (chooseTrade 5 ℚ.decℚ≤?) ≡ 3
fee-five-risk = refl

boundary-four-trades : chosenWeight (chooseTrade 4 ℚ.decℚ≤?) ≡ target
boundary-four-trades = refl

boundary-four-risk : riskValue (chooseTrade 4 ℚ.decℚ≤?) ≡ 3
boundary-four-risk = ℝ!

-- The executable result certifies an attained global minimum, so its own
-- exact risk value is an accepted budget and a lower bound on every rival.
chosen-budget-accepted : ∀ s (trade : CertifiedTrade s) →
  Risk.Accepted (netLoss s (chosenWeight trade)) (riskValue trade)
chosen-budget-accepted s trade =
  Laws.CVaR-bound→accepted (netLoss s (chosenWeight trade)) (riskValue trade)
    (riskValue trade) (CVaR-value trade) (≤ᵣ-refl (riskValue trade))

-- The optimizer has an exact rational value when its fee input is rational.
-- This specialized case permits a complete budget decision: unlike coarse
-- reports, it has neither approximation error nor a primal/dual gap.
chosenRisk : ℚ → ℚ
chosenRisk s with ℚ.≤Dec s 4
... | yes _ = 2 ℚ.+ s ℚ.· [ 1 / 4 ]
... | no _ = 3

chosen-risk-exact : ∀ s s₊ → riskValue (chooseTrade s s₊) ≡ rat (chosenRisk s)
chosen-risk-exact s s₊ with ℚ.≤Dec s 4
... | yes _ = cong (2 +ᵣ_) (sym (rat·ᵣrat s [ 1 / 4 ]))
  ∙ +ᵣ-rat 2 (s ℚ.· [ 1 / 4 ])
... | no _ = refl

chosenLoss : (s : ℚ) → 0 ℚ.≤ s → Vector 4
chosenLoss s s₊ = netLoss (rat s) (chosenWeight (chooseTrade s s₊))

chosen-CVaR : ∀ s s₊ → Risk.IsCVaR (chosenLoss s s₊) (rat (chosenRisk s))
chosen-CVaR s s₊ = subst (Risk.IsCVaR (chosenLoss s s₊)) (chosen-risk-exact s s₊)
  (CVaR-value (chooseTrade s s₊))

checkChosenBudget : ∀ s s₊ budget → Dec (Risk.Accepted (chosenLoss s s₊) (rat budget))
checkChosenBudget s s₊ budget with ℚ.≤Dec (chosenRisk s) budget
... | yes within = yes
  (Laws.CVaR-bound→accepted (chosenLoss s s₊) (rat (chosenRisk s)) (rat budget)
    (chosen-CVaR s s₊) (≤ℚ→≤ᵣ (chosenRisk s) budget within))
... | no exceeds = no λ accepted → exceeds
  (≤ᵣ→≤ℚ (chosenRisk s) budget
    (Laws.CVaR-accepted→bound (chosenLoss s s₊) (rat (chosenRisk s)) (rat budget)
      (chosen-CVaR s s₊) accepted))

chosen-budget-decision : ∀ s s₊ budget → Decision
chosen-budget-decision s s₊ budget with checkChosenBudget s s₊ budget
... | yes _ = pass
... | no _ = fail

fee-one-budget-two-fails : chosen-budget-decision 1 ℚ.decℚ≤? 2 ≡ fail
fee-one-budget-two-fails = refl

fee-one-exact-budget-passes : chosen-budget-decision 1 ℚ.decℚ≤? [ 9 / 4 ] ≡ pass
fee-one-exact-budget-passes = refl

fee-five-budget-three-passes : chosen-budget-decision 5 ℚ.decℚ≤? 3 ≡ pass
fee-five-budget-three-passes = refl

boundary-four-budget-three-passes : chosen-budget-decision 4 ℚ.decℚ≤? 3 ≡ pass
boundary-four-budget-three-passes = refl
