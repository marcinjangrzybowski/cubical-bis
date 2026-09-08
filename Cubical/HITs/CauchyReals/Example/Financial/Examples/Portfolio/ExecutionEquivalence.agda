{-# OPTIONS --safe --cubical #-}

-- Proportional absolute-trade costs follow ../../REFERENCES.md#boyd-2017.
-- The rates (1,1,3) are synthetic. The distinction between raw-loss and
-- cost-aware quotient classes is a cubical invariance result proved here;
-- equal market cashflows alone do not establish equal execution costs.

module Cubical.HITs.CauchyReals.Example.Financial.Examples.Portfolio.ExecutionEquivalence where

open import Cubical.HITs.CauchyReals.Example.Financial.Portfolio.ExecutionEquivalence
open import Cubical.HITs.CauchyReals.Example.Financial.Portfolio.Base public
open import Cubical.HITs.CauchyReals.Example.Financial.Core.EconomicEquivalence
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.RiskLaws
open import Cubical.HITs.CauchyReals.Algebra.Order.AbsoluteValue using (absᵣNonNeg)
open import Cubical.HITs.CauchyReals.Algebra.Order.Properties using (isIrrefl<ᵣ)
open import Cubical.Foundations.Equiv
open import Cubical.Data.Empty using (⊥)
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
import Cubical.Data.FinData.Base as F
import Cubical.HITs.SetQuotients as SQ
import Cubical.HITs.CauchyReals.Example.Financial.Portfolio.TransactionCosts as TC
import Cubical.HITs.CauchyReals.Example.Financial.Examples.Portfolio.Application as A
import Cubical.HITs.CauchyReals.Example.Financial.Examples.Portfolio.Diversification as D

-- A concrete invariance boundary: the direct balanced holding and its
-- wrapped basket have identical market losses but different execution fees.
-- Units match the existing example's loss units. These illustrative rates
-- are deliberately large enough to make the distinction transparent.
rates initial directHoldings basketHoldings : Vector 3
rates = A.three 1 1 3
initial = λ _ → 0
directHoldings = probability A.direct
basketHoldings = probability A.basket

rates-nonnegative : ∀ i → 0 ≤ᵣ rates i
rates-nonnegative F.zero = decℚ≤ᵣ?
rates-nonnegative (F.suc F.zero) = decℚ≤ᵣ?
rates-nonnegative (F.suc (F.suc F.zero)) = decℚ≤ᵣ?

module Example = ExecutionModel A.market rates initial
module Tail = TailRisk D.equalProbability D.halfTail
module Laws = CVaRLaws D.equalProbability D.halfTail
module Costs = TC.TailCosts D.equalProbability D.halfTail

raw-equivalent : directHoldings Example.Raw.≈ᴱ basketHoldings
raw-equivalent = funExt⁻ (A.direct-loss ∙ sym A.basket-loss)

same-raw-class : Example.Raw.class directHoldings ≡ Example.Raw.class basketHoldings
same-raw-class = Example.Raw.class-sound raw-equivalent

private
  cost-from-zero : ∀ {m} (rates holdings : Vector m) → (∀ i → 0 ≤ᵣ holdings i) →
    TC.transactionCost rates (λ _ → 0) holdings ≡ dot rates holdings
  cost-from-zero rates holdings nonnegative = sum-cong _ _ λ i →
    cong (rates i ·ᵣ_) (cong absᵣ (difference-zero (holdings i))
      ∙ absᵣNonNeg (holdings i) (nonnegative i))
    where
    difference-zero : ∀ x → x -ᵣ 0 ≡ x
    difference-zero x = ℝ!

direct-fee : Example.cost directHoldings ≡ 1
direct-fee = cost-from-zero rates directHoldings (probability-nonnegative A.direct) ∙ ℝ!

basket-fee : Example.cost basketHoldings ≡ 3
basket-fee = cost-from-zero rates basketHoldings (probability-nonnegative A.basket) ∙ ℝ!

unequal-fees : Example.cost directHoldings ≡ Example.cost basketHoldings → ⊥
unequal-fees same = isIrrefl<ᵣ 1
  (isTrans<≡ᵣ 1 3 1 decℚ<ᵣ? (sym (sym direct-fee ∙ same ∙ basket-fee)))

different-execution-classes :
  Example.Net.class directHoldings ≡ Example.Net.class basketHoldings → ⊥
different-execution-classes same = unequal-fees
  (Example.execution-equality-implies-equal-costs directHoldings basketHoldings
    raw-equivalent (Example.Net.class-effective same))

-- The original raw-loss quotient cannot support this execution map.
-- Reusing EconomicModel with allInLoss gives the correct quotient instead.
no-raw-to-execution-map :
  (f : Example.Raw.EconomicClass → Example.Net.EconomicClass) →
  (∀ u → f (Example.Raw.class u) ≡ Example.Net.class u) → ⊥
no-raw-to-execution-map f agrees = unequal-fees
  (Example.execution-descent-implies-cost-invariant f agrees
    directHoldings basketHoldings raw-equivalent)

directNet basketNet : Vector 4
directNet = TC.allInLoss A.market rates initial directHoldings
basketNet = TC.allInLoss A.market rates initial basketHoldings

direct-net-CVaR : Tail.IsCVaR directNet 3
direct-net-CVaR = subst (Tail.IsCVaR directNet)
  (cong (_+ᵣ 2) direct-fee ∙ arithmetic)
  (Costs.allIn-CVaR A.market rates initial directHoldings 2
    (subst (λ X → Tail.IsCVaR X 2) (sym A.direct-loss) D.CVaR-balanced))
  where
  arithmetic : 1 +ᵣ 2 ≡ 3
  arithmetic = ℝ!

basket-net-CVaR : Tail.IsCVaR basketNet 5
basket-net-CVaR = subst (Tail.IsCVaR basketNet)
  (cong (_+ᵣ 2) basket-fee ∙ arithmetic)
  (Costs.allIn-CVaR A.market rates initial basketHoldings 2
    (subst (λ X → Tail.IsCVaR X 2) (sym A.basket-loss) D.CVaR-balanced))
  where
  arithmetic : 3 +ᵣ 2 ≡ 5
  arithmetic = ℝ!

direct-approved-at-three : Tail.Accepted directNet 3
direct-approved-at-three = Laws.CVaR-bound→accepted directNet 3 3 direct-net-CVaR (≤ᵣ-refl 3)

basket-rejected-at-three : Tail.Accepted basketNet 3 → ⊥
basket-rejected-at-three accepted = isIrrefl<ᵣ 3
  (isTrans<≤ᵣ 3 5 3 decℚ<ᵣ?
    (Laws.CVaR-accepted→bound basketNet 5 3 basket-net-CVaR accepted))
