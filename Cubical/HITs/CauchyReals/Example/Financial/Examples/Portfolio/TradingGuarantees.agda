{-# OPTIONS --safe --cubical #-}

-- System guarantee for the synthetic proportional-cost CVaR market:
-- ../../REFERENCES.md#boyd-2017 and #rockafellar-uryasev-2002.
-- The solver below decides existence of an acceptable fully invested
-- real portfolio, and returns an executable allocation when one exists.
-- Its completeness is specific to this proved market and fee model.

module Cubical.HITs.CauchyReals.Example.Financial.Examples.Portfolio.TradingGuarantees where

open import Cubical.HITs.CauchyReals.Example.Financial.Portfolio.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals using (ℚ; module ℚ; [_/_]; fromNatℚ)
open import Cubical.Data.NatPlusOne using (fromNatℕ₊₁)
open import Cubical.Data.Int.Base using (fromNatℤ)
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Data.Bool using (Bool; true; false; isSetBool; true≢false; false≢true)
open import Cubical.Data.Empty using (⊥; isProp⊥) renaming (rec to absurd)
open import Cubical.Relation.Nullary using (Dec; yes; no; ¬_)
open import Cubical.Foundations.Equiv using (_≃_; propBiimpl→Equiv)
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
import Cubical.Data.FinData.Base as F
import Cubical.HITs.PropositionalTruncation as PT
import Cubical.HITs.CauchyReals.Example.Financial.Portfolio.TransactionCosts as TC
import Cubical.HITs.CauchyReals.Example.Financial.Examples.Portfolio.Diversification as D
import Cubical.HITs.CauchyReals.Example.Financial.Examples.Portfolio.Rebalancing as R
import Cubical.HITs.CauchyReals.Example.Financial.Examples.Portfolio.TradeDecision as T

module Risk = R.Risk
module Laws = R.Laws

-- Every signed two-asset holding with sum one is represented. No sign
-- decision or long-only restriction is imposed on competing portfolios.
holdings-complete : (u : Vector 2) → sum u ≡ 1 → u ≡ R.holdings (u F.zero)
holdings-complete u total = funExt λ
  { F.zero → refl
  ; (F.suc F.zero) → sym (recover (u F.zero) (u (F.suc F.zero)))
      ∙ cong (_-ᵣ u F.zero) total
  }
  where
  recover : ∀ x y → (x +ᵣ (y +ᵣ 0)) -ᵣ x ≡ y
  recover x y = ℝ!

-- Actual loss means the existing mathematical execution model: each leg
-- pays the proportional fee s/2 on its absolute traded amount. This is
-- not an exchange fill, a funded cash ledger, or a market-data calibration.
executionLoss : ℚ → Vector 2 → Vector 4
executionLoss s = TC.allInLoss R.market (R.rates (rat s)) R.initial

execution-implementation : ∀ s (u : Vector 2) → sum u ≡ 1 →
  executionLoss s u ≡ R.netLoss (rat s) (u F.zero)
execution-implementation s u total = cong (executionLoss s) (holdings-complete u total)
  ∙ R.netLoss-implementation (rat s) (u F.zero)

FeasibleOrder : ℚ → ℚ → Type₀
FeasibleOrder s budget = Σ[ u ∈ Vector 2 ]
  ((sum u ≡ 1) × Risk.Accepted (executionLoss s u) (rat budget))

-- Hiding a feasible competitor must not hide the strength of the claim:
-- existence ranges over arbitrary real holdings, including short positions.
Feasible : ℚ → ℚ → Type₀
Feasible s budget = PT.∥ FeasibleOrder s budget ∥₁

AllRejected : ℚ → ℚ → Type₀
AllRejected s budget = (u : Vector 2) → sum u ≡ 1 →
  ¬ Risk.Accepted (executionLoss s u) (rat budget)

chosen-global-lower : ∀ s s₊ (u : Vector 2) → sum u ≡ 1 → ∀ t →
  rat (T.chosenRisk s) ≤ᵣ Risk.objective (executionLoss s u) t
chosen-global-lower s s₊ u total t = isTrans≡≤ᵣ _ _ _
  (sym (T.chosen-risk-exact s s₊))
  (isTrans≤≡ᵣ _ _ _ (T.global-bound (T.chooseTrade s s₊) (u F.zero) t)
    (sym (cong (λ X → Risk.objective X t) (execution-implementation s u total))))

competitor-budget-bound : ∀ s s₊ budget (u : Vector 2) → sum u ≡ 1 →
  Risk.Accepted (executionLoss s u) (rat budget) →
  rat (T.chosenRisk s) ≤ᵣ rat budget
competitor-budget-bound s s₊ budget u total = PT.rec (isProp≤ᵣ _ _)
  (λ (t , accepted) → isTrans≤ᵣ _ _ _ (chosen-global-lower s s₊ u total t) accepted)

competitor→chosen : ∀ s s₊ budget (u : Vector 2) → sum u ≡ 1 →
  Risk.Accepted (executionLoss s u) (rat budget) →
  Risk.Accepted (T.chosenLoss s s₊) (rat budget)
competitor→chosen s s₊ budget u total accepted = Laws.CVaR-bound→accepted
  (T.chosenLoss s s₊) (rat (T.chosenRisk s)) (rat budget) (T.chosen-CVaR s s₊)
  (competitor-budget-bound s s₊ budget u total accepted)

feasible→chosen : ∀ s s₊ budget → Feasible s budget →
  Risk.Accepted (T.chosenLoss s s₊) (rat budget)
feasible→chosen s s₊ budget = PT.rec (Risk.accepted-isProp (T.chosenLoss s s₊) (rat budget))
  (λ (u , total , accepted) → competitor→chosen s s₊ budget u total accepted)

-- A successful result contains usable holdings, not just truncated
-- existence. The Allocation type already proves nonnegative coordinates
-- and total weight one. The remaining fields refer to the actual fee model.
record ApprovedTrade (s budget : ℚ) : Type₀ where
  field
    selected : Allocation 2
    rates-valid : ∀ i → 0 ≤ᵣ R.rates (rat s) i
    acceptance : Risk.Accepted (executionLoss s (probability selected)) (rat budget)
    exact-risk : Risk.IsCVaR (executionLoss s (probability selected)) (rat (T.chosenRisk s))
    globally-optimal : (u : Vector 2) → sum u ≡ 1 → ∀ t →
      rat (T.chosenRisk s) ≤ᵣ Risk.objective (executionLoss s u) t

  selectedWeight : ℝ
  selectedWeight = probability selected F.zero

  executedLoss : Vector 4
  executedLoss = executionLoss s (probability selected)

  market-agrees : portfolioLoss R.market (probability selected) ≡ D.mixed selectedWeight
  market-agrees = cong (portfolioLoss R.market)
    (holdings-complete (probability selected) (probability-total selected))
    ∙ R.holdings-loss selectedWeight

  fee-agrees : TC.transactionCost (R.rates (rat s)) R.initial (probability selected)
    ≡ R.fee (rat s) selectedWeight
  fee-agrees = cong (TC.transactionCost (R.rates (rat s)) R.initial)
    (holdings-complete (probability selected) (probability-total selected))
    ∙ R.fee-implementation (rat s) selectedWeight

  execution-agrees : executedLoss ≡ R.netLoss (rat s) selectedWeight
  execution-agrees = execution-implementation s (probability selected) (probability-total selected)

  risk-within-budget : rat (T.chosenRisk s) ≤ᵣ rat budget
  risk-within-budget = Laws.CVaR-accepted→bound executedLoss
    (rat (T.chosenRisk s)) (rat budget) exact-risk acceptance

  -- Competitors need not supply a preferred minimizing threshold. A merely
  -- attained CVaR value suffices, using elimination into an order proposition.
  risk-no-larger : (u : Vector 2) → sum u ≡ 1 → ∀ r →
    Risk.IsCVaR (executionLoss s u) r → rat (T.chosenRisk s) ≤ᵣ r
  risk-no-larger u total r cvar = PT.rec (isProp≤ᵣ _ _)
    (λ (t , exact) → isTrans≤≡ᵣ _ _ _ (globally-optimal u total t) exact)
    (snd cvar)
open ApprovedTrade public

approveChosen : ∀ s s₊ budget →
  Risk.Accepted (T.chosenLoss s s₊) (rat budget) → ApprovedTrade s budget
approveChosen s s₊ budget accepted .selected = T.chosenAllocation (rat s) (T.chooseTrade s s₊)
approveChosen s s₊ budget accepted .rates-valid = R.rates-nonnegative (rat s) (≤ℚ→≤ᵣ 0 s s₊)
approveChosen s s₊ budget accepted .acceptance = subst
  (λ X → Risk.Accepted X (rat budget))
  (sym (R.netLoss-implementation (rat s) (T.chosenWeight (T.chooseTrade s s₊)))) accepted
approveChosen s s₊ budget accepted .exact-risk = subst
  (λ X → Risk.IsCVaR X (rat (T.chosenRisk s)))
  (sym (R.netLoss-implementation (rat s) (T.chosenWeight (T.chooseTrade s s₊))))
  (T.chosen-CVaR s s₊)
approveChosen s s₊ budget accepted .globally-optimal = chosen-global-lower s s₊

approved→feasible : ∀ s budget → ApprovedTrade s budget → Feasible s budget
approved→feasible s budget trade = PT.∣ probability (selected trade) ,
  probability-total (selected trade) , acceptance trade ∣₁

chosen→feasible : ∀ s s₊ budget →
  Risk.Accepted (T.chosenLoss s s₊) (rat budget) → Feasible s budget
chosen→feasible s s₊ budget accepted = approved→feasible s budget
  (approveChosen s s₊ budget accepted)

-- This is the key completeness result: restricting the check to the
-- computed optimizer loses no feasible signed real fully invested holding.
feasible≃chosen : ∀ s s₊ budget → Feasible s budget ≃
  Risk.Accepted (T.chosenLoss s s₊) (rat budget)
feasible≃chosen s s₊ budget = propBiimpl→Equiv PT.squash₁
  (Risk.accepted-isProp (T.chosenLoss s s₊) (rat budget))
  (feasible→chosen s s₊ budget) (chosen→feasible s s₊ budget)

-- Recover a usable certified order from mere feasibility without choosing
-- its hidden witness: compute the fixed optimizer and transfer its budget
-- certificate. This is not a general elimination of truncation into data.
reconstructTrade : ∀ s s₊ budget → Feasible s budget → ApprovedTrade s budget
reconstructTrade s s₊ budget feasible =
  approveChosen s s₊ budget (feasible→chosen s s₊ budget feasible)

all-rejected→infeasible : ∀ s budget → AllRejected s budget → ¬ Feasible s budget
all-rejected→infeasible s budget rejected = PT.rec isProp⊥
  (λ (u , total , accepted) → rejected u total accepted)

-- There is no inconclusive constructor. Rational comparisons are complete
-- here because this market has a computed optimizer with an exact rational
-- value; arbitrary Cauchy-real order is never decided.
data TradeResult (s budget : ℚ) : Type₀ where
  execute : ApprovedTrade s budget → TradeResult s budget
  reject : AllRejected s budget → TradeResult s budget

solve : (s : ℚ) → 0 ℚ.≤ s → (budget : ℚ) → TradeResult s budget
solve s s₊ budget with T.checkChosenBudget s s₊ budget
... | yes accepted = execute (approveChosen s s₊ budget accepted)
... | no notAccepted = reject
  (λ u total accepted → notAccepted (competitor→chosen s s₊ budget u total accepted))

passes : ∀ {s budget} → TradeResult s budget → Bool
passes (execute trade) = true
passes (reject rejected) = false

success-certificate : ∀ {s budget} (result : TradeResult s budget) →
  passes result ≡ true → ApprovedTrade s budget
success-certificate (execute trade) proof = trade
success-certificate (reject rejected) proof = absurd (false≢true proof)

failure-certificate : ∀ {s budget} (result : TradeResult s budget) →
  passes result ≡ false → AllRejected s budget
failure-certificate (execute trade) proof = absurd (true≢false proof)
failure-certificate (reject rejected) proof = rejected

result-sound : ∀ s budget (result : TradeResult s budget) →
  passes result ≡ true → Feasible s budget
result-sound s budget result proof = approved→feasible s budget (success-certificate result proof)

result-complete : ∀ s budget (result : TradeResult s budget) →
  Feasible s budget → passes result ≡ true
result-complete s budget (execute trade) feasible = refl
result-complete s budget (reject rejected) feasible =
  absurd (all-rejected→infeasible s budget rejected feasible)

-- A cubical equivalence and its univalent path identify the Boolean
-- success condition with propositionally truncated real feasibility.
-- The returned allocation is computed directly, not chosen from truncation.
solver-pass≃feasible : ∀ s s₊ budget →
  (passes (solve s s₊ budget) ≡ true) ≃ Feasible s budget
solver-pass≃feasible s s₊ budget = propBiimpl→Equiv (isSetBool _ _) PT.squash₁
  (result-sound s budget (solve s s₊ budget))
  (result-complete s budget (solve s s₊ budget))

solver-policy-path : ∀ s s₊ budget →
  (passes (solve s s₊ budget) ≡ true) ≡ Feasible s budget
solver-policy-path s s₊ budget = ua (solver-pass≃feasible s s₊ budget)

decideFeasible : (s : ℚ) → 0 ℚ.≤ s → (budget : ℚ) → Dec (Feasible s budget)
decideFeasible s s₊ budget with solve s s₊ budget
... | execute trade = yes (approved→feasible s budget trade)
... | reject rejected = no (all-rejected→infeasible s budget rejected)

-- Both verdicts compute by rational comparisons. Failure at budget 2 is
-- now an impossibility theorem for ALL real fully invested competitors,
-- rather than a report about the particular order chosen by the algorithm.
fee-one-budget-two-rejects : passes (solve 1 ℚ.decℚ≤? 2) ≡ false
fee-one-budget-two-rejects = refl

fee-one-budget-two-impossible : AllRejected 1 2
fee-one-budget-two-impossible = failure-certificate (solve 1 ℚ.decℚ≤? 2)
  fee-one-budget-two-rejects

fee-one-budget-two-infeasible : ¬ Feasible 1 2
fee-one-budget-two-infeasible = all-rejected→infeasible 1 2 fee-one-budget-two-impossible

fee-one-exact-budget-passes : passes (solve 1 ℚ.decℚ≤? [ 9 / 4 ]) ≡ true
fee-one-exact-budget-passes = refl

fee-one-approved : ApprovedTrade 1 [ 9 / 4 ]
fee-one-approved = success-certificate (solve 1 ℚ.decℚ≤? [ 9 / 4 ]) fee-one-exact-budget-passes

fee-one-feasible : Feasible 1 [ 9 / 4 ]
fee-one-feasible = approved→feasible 1 [ 9 / 4 ] fee-one-approved

fee-one-allocation : probability (selected fee-one-approved)
  ≡ R.two (rat [ 3 / 4 ]) (rat [ 1 / 4 ])
fee-one-allocation = funExt λ
  { F.zero → refl
  ; (F.suc F.zero) → ℝ!
  }

fee-one-actual-cost :
  TC.transactionCost (R.rates 1) R.initial (probability (selected fee-one-approved))
    ≡ rat [ 1 / 4 ]
fee-one-actual-cost = fee-agrees fee-one-approved ∙ R.fee-target 1 ∙ ℝ!

fee-one-global-risk : (u : Vector 2) → sum u ≡ 1 → ∀ r →
  Risk.IsCVaR (executionLoss 1 u) r → rat [ 9 / 4 ] ≤ᵣ r
fee-one-global-risk u total r cvar = isTrans≡≤ᵣ _ _ _ ℝ!
  (risk-no-larger fee-one-approved u total r cvar)
