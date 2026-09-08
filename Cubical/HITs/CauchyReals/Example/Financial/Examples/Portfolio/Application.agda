-- CVaR threshold and dual certificates motivate these executable risk reports:
-- ../../REFERENCES.md#rockafellar-uryasev-2002 and #shapiro-2016.
-- The four scenarios and 50% tail are synthetic; the economic quotient and
-- its certified policy paths are constructions proved in this development.

module Cubical.HITs.CauchyReals.Example.Financial.Examples.Portfolio.Application where

open import Cubical.HITs.CauchyReals.Example.Financial.Core.Vectors public using (three)

open import Cubical.HITs.CauchyReals.Example.Financial.Portfolio.Policy
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.RiskControl
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.WorstCase
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.ExpectedShortfall
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Rationals.Base using (fromNatℚ)
import Cubical.HITs.CauchyReals.Example.Financial.Examples.Portfolio.Diversification as D
import Cubical.Data.FinData.Base as F

module Audit = Control D.equalProbability D.halfTail
module ES = TailRisk D.equalProbability D.halfTail
module Policy = RiskPolicy D.equalProbability D.halfTail

-- Exact primal/dual reports are executable inputs to the budget checker.
balanced-report : Audit.Report D.balanced
balanced-report .Audit.Report.trialThreshold = 0
balanced-report .Audit.Report.stressDistribution = D.dualBalanced
balanced-report .Audit.Report.densityBound = D.dualBalanced-admissible
balanced-report .Audit.Report.lower = 2
balanced-report .Audit.Report.upper = 2
balanced-report .Audit.Report.lower-valid = ≡ᵣWeaken≤ᵣ _ _ (sym (D.dual-value-mixed D.half))
balanced-report .Audit.Report.upper-valid = ≡ᵣWeaken≤ᵣ _ _ D.objective-balanced

concentrated-report : Audit.Report D.assetA
concentrated-report .Audit.Report.trialThreshold = 0
concentrated-report .Audit.Report.stressDistribution = D.dualA
concentrated-report .Audit.Report.densityBound = D.dualA-admissible
concentrated-report .Audit.Report.lower = 3
concentrated-report .Audit.Report.upper = 3
concentrated-report .Audit.Report.lower-valid = ≡ᵣWeaken≤ᵣ _ _ (sym D.dual-value-A)
concentrated-report .Audit.Report.upper-valid = ≡ᵣWeaken≤ᵣ _ _ D.objective-A

-- Wider bounds illustrate why failure to prove safety is not rejection.
coarse-report : Audit.Report D.balanced
coarse-report .Audit.Report.trialThreshold = 0
coarse-report .Audit.Report.stressDistribution = D.dualBalanced
coarse-report .Audit.Report.densityBound = D.dualBalanced-admissible
coarse-report .Audit.Report.lower = 1
coarse-report .Audit.Report.upper = 3
coarse-report .Audit.Report.lower-valid =
  isTrans≤≡ᵣ _ _ _ decℚ≤ᵣ? (sym (D.dual-value-mixed D.half))
coarse-report .Audit.Report.upper-valid = isTrans≡≤ᵣ _ _ _ D.objective-balanced decℚ≤ᵣ?

-- These are checked by reduction of rational comparisons. The results also
-- carry proof objects, via Audit.check-sound, and not just Boolean labels.
balanced-passes-budget-two : Audit.decision (Audit.check D.balanced balanced-report 2) ≡ pass
balanced-passes-budget-two = refl

balanced-fails-budget-one : Audit.decision (Audit.check D.balanced balanced-report 1) ≡ fail
balanced-fails-budget-one = refl

concentration-fails-budget-two : Audit.decision (Audit.check D.assetA concentrated-report 2) ≡ fail
concentration-fails-budget-two = refl

coarse-report-is-inconclusive : Audit.decision (Audit.check D.balanced coarse-report 2) ≡ unknown
coarse-report-is-inconclusive = refl

approved-balanced : ES.Accepted D.balanced 2
approved-balanced = Audit.check-sound D.balanced balanced-report 2

rejected-concentration : ES.Accepted D.assetA 2 → ⊥
rejected-concentration = Audit.check-sound D.assetA concentrated-report 2

-- The third instrument wraps the equal-weight basket. The direct two-asset
-- implementation and a holding of the wrapped basket are economically equal.
market : Market 3 4
market F.zero = D.assetA
market (F.suc F.zero) = D.assetB
market (F.suc (F.suc F.zero)) = D.balanced

direct basket : Allocation 3
direct = three D.half D.half 0 , nonnegative , total
  where
  nonnegative : ∀ i → 0 ≤ᵣ three D.half D.half 0 i
  nonnegative F.zero = decℚ≤ᵣ?
  nonnegative (F.suc F.zero) = decℚ≤ᵣ?
  nonnegative (F.suc (F.suc F.zero)) = decℚ≤ᵣ?
  total : sum (three D.half D.half 0) ≡ 1
  total = ℝ!
basket = three 0 0 1 , nonnegative , total
  where
  nonnegative : ∀ i → 0 ≤ᵣ three 0 0 1 i
  nonnegative F.zero = decℚ≤ᵣ?
  nonnegative (F.suc F.zero) = decℚ≤ᵣ?
  nonnegative (F.suc (F.suc F.zero)) = decℚ≤ᵣ?
  total : sum (three 0 0 1) ≡ 1
  total = ℝ!

direct-loss : portfolioLoss market (probability direct) ≡ D.balanced
direct-loss = funExt (λ i → ℝ!)

basket-loss : portfolioLoss market (probability basket) ≡ D.balanced
basket-loss = funExt (λ i → ℝ!)

policyLimits : Limits
policyLimits = limits 1 2 2

balanced-compliant : Policy.Satisfies policyLimits D.balanced
balanced-compliant = ≡ᵣWeaken≤ᵣ _ _ D.mean-balanced ,
  worstCase-least D.balanced 2
    (λ i → isTrans≡≤ᵣ _ _ _ (funExt⁻ D.balanced-values i) (bound i)) ,
  approved-balanced
  where
  bound : ∀ i → D.four 2 2 0 0 i ≤ᵣ 2
  bound F.zero = decℚ≤ᵣ?
  bound (F.suc F.zero) = decℚ≤ᵣ?
  bound (F.suc (F.suc F.zero)) = decℚ≤ᵣ?
  bound (F.suc (F.suc (F.suc F.zero))) = decℚ≤ᵣ?

module Managed = Policy.ManagedMarket market policyLimits

direct-certified basket-certified : Managed.CertifiedAllocation
direct-certified = direct , subst (Policy.Satisfies policyLimits) (sym direct-loss) balanced-compliant
basket-certified = basket , subst (Policy.Satisfies policyLimits) (sym basket-loss) balanced-compliant

-- Actual use of the cubical quotient: differently implemented holdings,
-- including all their policy proofs, define the same certified economic class.
netting-preserves-certified-class :
  Managed.forget-representation direct-certified ≡ Managed.forget-representation basket-certified
netting-preserves-certified-class = Managed.netting-path direct-certified basket-certified
  (funExt⁻ (direct-loss ∙ sym basket-loss))

-- A certificate for every point of a real rebalancing segment, without
-- identifying distinct real holdings by cubical equality.
certified-transition : UnitWeight → Managed.CertifiedAllocation
certified-transition w = Managed.rebalance-certified w direct-certified basket-certified

-- A verified one-sided scenario error bound transports the certificate to
-- budget ε + 2, with coefficient one on ε. This is an upper allowance, not
-- a claim that the actual minimum capital changes by exactly that amount.
model-error-reserve : ∀ (actual : Vector 4) ε →
  (∀ i → actual i ≤ᵣ ε +ᵣ D.balanced i) → ES.Accepted actual (ε +ᵣ 2)
model-error-reserve actual ε error-bound =
  ES.accepted-perturbation actual D.balanced ε 2 error-bound approved-balanced
