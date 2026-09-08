-- Proportional trading costs and CVaR motivate the rebalancing objective:
-- ../../REFERENCES.md#boyd-2017 and #rockafellar-uryasev-2002.
-- Both traded legs are charged at s/2, giving s |1-w|; distinguish L1 traded
-- amount from half-L1 turnover. Fees and the resulting threshold 4 are
-- synthetic parameters of this market; see #synthetic-parameters.

module Cubical.HITs.CauchyReals.Example.Financial.Examples.Portfolio.Rebalancing where

open import Cubical.HITs.CauchyReals.Example.Financial.Core.Vectors public using (two)

open import Cubical.HITs.CauchyReals.Example.Financial.Risk.RiskLaws
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.Shortfall
open import Cubical.HITs.CauchyReals.Algebra.Order.AbsoluteValue
open import Cubical.HITs.CauchyReals.Algebra.Order.Lattice using (≤maxᵣ)
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition.Properties
open import Cubical.HITs.CauchyReals.Algebra.Order.Properties using (isIrrefl<ᵣ)
open import Cubical.HITs.CauchyReals.Foundation.Rationals using ([_/_])
open import Cubical.Data.NatPlusOne using (fromNatℕ₊₁)
open import Cubical.Data.Int.Base using (fromNatℤ)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
import Cubical.HITs.CauchyReals.Example.Financial.Examples.Portfolio.Diversification as D
import Cubical.HITs.CauchyReals.Example.Financial.Portfolio.TransactionCosts as TC
open import Cubical.HITs.CauchyReals.Example.Financial.Portfolio.Base using (Market; portfolioLoss)
import Cubical.Data.FinData.Base as F
import Cubical.HITs.PropositionalTruncation as PT

module Risk = TailRisk D.equalProbability D.halfTail
module Laws = CVaRLaws D.equalProbability D.halfTail
module Costs = TC.TailCosts D.equalProbability D.halfTail

-- Start with one unit of A and zero B. The effective fee s charges
-- s*|1-w| to move to (w,1-w); each traded leg has unit rate s/2.
fee : ℝ → ℝ → ℝ
fee s w = s ·ᵣ absᵣ (1 -ᵣ w)

netLoss : ℝ → ℝ → Vector 4
netLoss s w i = fee s w +ᵣ D.mixed w i

target : ℝ
target = rat [ 3 / 4 ]

private
  absolute-upper : ∀ x → x ≤ᵣ absᵣ x
  absolute-upper x = isTrans≤≡ᵣ _ _ _ (≤maxᵣ x (-ᵣ x)) (sym (abs-max x))

  one-minus-target : 1 -ᵣ target ≡ D.quarter
  one-minus-target = ℝ!

  one-minus-half : 1 -ᵣ D.half ≡ D.half
  one-minus-half = ℝ!

fee-target : ∀ s → fee s target ≡ s ·ᵣ D.quarter
fee-target s = cong (s ·ᵣ_)
  (cong absᵣ one-minus-target ∙ absᵣNonNeg D.quarter decℚ≤ᵣ?)

fee-balanced : ∀ s → fee s D.half ≡ s ·ᵣ D.half
fee-balanced s = cong (s ·ᵣ_)
  (cong absᵣ one-minus-half ∙ absᵣNonNeg D.half decℚ≤ᵣ?)

fee-no-trade : ∀ s → fee s 1 ≡ 0
fee-no-trade s = cong (s ·ᵣ_) (cong absᵣ (+-ᵣ 1) ∙ absᵣ0)
  ∙ Rℝ.0RightAnnihilates s

fee-nonnegative : ∀ s w → 0 ≤ᵣ s → 0 ≤ᵣ fee s w
fee-nonnegative s w s₊ = nonnegative-mul s _ s₊ (0≤absᵣ _)

-- The trading fee is a deterministic additional loss. All thresholds of
-- the net loss correspond to shifted thresholds of the underlying loss.
net-objective : ∀ s w t → Risk.objective (netLoss s w) t
  ≡ fee s w +ᵣ Risk.objective (D.mixed w) (t -ᵣ fee s w)
net-objective s w t = Costs.objective-cash-at (D.mixed w) (fee s w) t

target-values : D.mixed target ≡ D.four 4 0 0 0
target-values = funExt λ
  { F.zero → ℝ!
  ; (F.suc F.zero) → ℝ!
  ; (F.suc (F.suc F.zero)) → ℝ!
  ; (F.suc (F.suc (F.suc F.zero))) → ℝ!
  }

target-objective : Risk.objective (D.mixed target) 0 ≡ 2
target-objective = cong (λ X → Risk.objective X 0) target-values
  ∙ cong (λ X → 0 +ᵣ 2 ·ᵣ expectation D.equalProbability X) (funExt stops)
  ∙ ℝ!
  where
  stops : ∀ i → stopLoss (D.four 4 0 0 0 i) 0 ≡ D.four 4 0 0 0 i
  stops F.zero = stopLoss-at-zero 4 decℚ≤ᵣ?
  stops (F.suc F.zero) = stopLoss-zero-below 0 0 decℚ≤ᵣ?
  stops (F.suc (F.suc F.zero)) = stopLoss-zero-below 0 0 decℚ≤ᵣ?
  stops (F.suc (F.suc (F.suc F.zero))) = stopLoss-zero-below 0 0 decℚ≤ᵣ?

target-CVaR : Risk.IsCVaR (D.mixed target) 2
target-CVaR = D.all-portfolios-lower-bound target , PT.∣ 0 , target-objective ∣₁

target-net-CVaR : ∀ s → Risk.IsCVaR (netLoss s target) (2 +ᵣ s ·ᵣ D.quarter)
target-net-CVaR s = subst (Risk.IsCVaR (netLoss s target))
  (cong (_+ᵣ 2) (fee-target s) ∙ +ᵣComm _ 2)
  (Laws.IsCVaR-cash (D.mixed target) 2 (fee s target) target-CVaR)

balanced-net-CVaR : ∀ s → Risk.IsCVaR (netLoss s D.half) (2 +ᵣ s ·ᵣ D.half)
balanced-net-CVaR s = subst (Risk.IsCVaR (netLoss s D.half))
  (cong (_+ᵣ 2) (fee-balanced s) ∙ +ᵣComm _ 2)
  (Laws.IsCVaR-cash D.balanced 2 (fee s D.half) D.CVaR-balanced)

no-trade-loss : ∀ s → netLoss s 1 ≡ D.assetA
no-trade-loss s = funExt λ i → cong (_+ᵣ D.mixed 1 i) (fee-no-trade s) ∙ ℝ!

no-trade-CVaR : ∀ s → Risk.IsCVaR (netLoss s 1) 3
no-trade-CVaR s = subst (λ X → Risk.IsCVaR X 3) (sym (no-trade-loss s)) D.CVaR-A

private
  -- Two admissible dual supports of the original CVaR objective.
  affine-dual-value : ∀ w → expectation D.dualA (D.mixed w) ≡ 4 ·ᵣ w -ᵣ 1
  affine-dual-value w = ℝ!

  affine-lower : ∀ w t → 4 ·ᵣ w -ᵣ 1 ≤ᵣ Risk.objective (D.mixed w) t
  affine-lower w t = isTrans≡≤ᵣ _ _ _ (sym (affine-dual-value w))
    (Risk.weak-duality (D.mixed w) D.dualA D.dualA-admissible t)

  small-fraction : ∀ s → 0 ≤ᵣ s → 0 ≤ᵣ s ·ᵣ D.quarter
  small-fraction s s₊ = nonnegative-mul s D.quarter s₊ decℚ≤ᵣ?

  fraction-at-most-one : ∀ s → s ≤ᵣ 4 → s ·ᵣ D.quarter ≤ᵣ 1
  fraction-at-most-one s s≤4 = isTrans≤≡ᵣ _ _ _
    (≤ᵣ-·ᵣo s 4 D.quarter decℚ≤ᵣ? s≤4) endpoint
    where
    endpoint : 4 ·ᵣ D.quarter ≡ 1
    endpoint = ℝ!

  supporting-line : ∀ s w t → 0 ≤ᵣ s → s ≤ᵣ 4 →
    (2 -ᵣ 3 ·ᵣ (s ·ᵣ D.quarter)) +ᵣ s ·ᵣ w
      ≤ᵣ Risk.objective (D.mixed w) t
  supporting-line s w t s₊ s≤4 = isTrans≡≤ᵣ _ _ _ expansion
    (isTrans≤≡ᵣ _ _ _
      (≤ᵣMonotone+ᵣ _ _ _ _
        (≤ᵣ-o·ᵣ _ _ (1 -ᵣ s ·ᵣ D.quarter)
          (x≤y→0≤y-x _ 1 (fraction-at-most-one s s≤4))
          (D.all-portfolios-lower-bound w t))
        (≤ᵣ-o·ᵣ _ _ (s ·ᵣ D.quarter) (small-fraction s s₊) (affine-lower w t)))
      combine)
    where
    expansion : (2 -ᵣ 3 ·ᵣ (s ·ᵣ D.quarter)) +ᵣ s ·ᵣ w ≡
      (1 -ᵣ s ·ᵣ D.quarter) ·ᵣ 2 +ᵣ (s ·ᵣ D.quarter) ·ᵣ (4 ·ᵣ w -ᵣ 1)
    expansion = ℝ!
    combine : (1 -ᵣ s ·ᵣ D.quarter) ·ᵣ Risk.objective (D.mixed w) t
      +ᵣ (s ·ᵣ D.quarter) ·ᵣ Risk.objective (D.mixed w) t
      ≡ Risk.objective (D.mixed w) t
    combine = ℝ!

-- LOW FEES: global bound for all real weights and all net-loss thresholds.
-- A real fee is never case-split; the hypotheses describe this regime.
low-fee-global-bound : ∀ s → 0 ≤ᵣ s → s ≤ᵣ 4 → ∀ w t →
  2 +ᵣ s ·ᵣ D.quarter ≤ᵣ Risk.objective (netLoss s w) t
low-fee-global-bound s s₊ s≤4 w t = isTrans≡≤ᵣ _ _ _ split
  (isTrans≤≡ᵣ _ _ _
    (≤ᵣMonotone+ᵣ _ _ _ _
      (≤ᵣ-o·ᵣ _ _ s s₊ (absolute-upper (1 -ᵣ w)))
      (supporting-line s w (t -ᵣ fee s w) s₊ s≤4))
    (sym (net-objective s w t)))
  where
  split : 2 +ᵣ s ·ᵣ D.quarter ≡ s ·ᵣ (1 -ᵣ w)
    +ᵣ ((2 -ᵣ 3 ·ᵣ (s ·ᵣ D.quarter)) +ᵣ s ·ᵣ w)
  split = ℝ!

-- HIGH FEES: the affine dual support plus turnover dominates the current
-- portfolio's risk. This also allows arbitrary shorted target holdings.
high-fee-global-bound : ∀ s → 4 ≤ᵣ s → ∀ w t →
  3 ≤ᵣ Risk.objective (netLoss s w) t
high-fee-global-bound s four≤s w t = isTrans≡≤ᵣ _ _ _ split
  (isTrans≤≡ᵣ _ _ _
    (≤ᵣMonotone+ᵣ _ _ _ _ fee-bound (affine-lower w (t -ᵣ fee s w)))
    (sym (net-objective s w t)))
  where
  split : 3 ≡ 4 ·ᵣ (1 -ᵣ w) +ᵣ (4 ·ᵣ w -ᵣ 1)
  split = ℝ!
  fee-bound : 4 ·ᵣ (1 -ᵣ w) ≤ᵣ fee s w
  fee-bound = isTrans≤ᵣ _ _ _
    (≤ᵣ-o·ᵣ _ _ 4 decℚ≤ᵣ? (absolute-upper (1 -ᵣ w)))
    (≤ᵣ-·ᵣo 4 s (absᵣ (1 -ᵣ w)) (0≤absᵣ _) four≤s)

target-net-objective : ∀ s → Risk.objective (netLoss s target) (fee s target)
  ≡ 2 +ᵣ s ·ᵣ D.quarter
target-net-objective s =
  cong (Risk.objective (netLoss s target)) (sym (+IdR (fee s target)))
  ∙ Risk.objective-cash (D.mixed target) 0 (fee s target)
  ∙ cong₂ _+ᵣ_ (fee-target s) target-objective ∙ +ᵣComm _ 2

low-fee-global-optimum : ∀ s → 0 ≤ᵣ s → s ≤ᵣ 4 → ∀ w t →
  Risk.objective (netLoss s target) (fee s target) ≤ᵣ Risk.objective (netLoss s w) t
low-fee-global-optimum s s₊ s≤4 w t =
  isTrans≡≤ᵣ _ _ _ (target-net-objective s) (low-fee-global-bound s s₊ s≤4 w t)

no-trade-objective : ∀ s → Risk.objective (netLoss s 1) 0 ≡ 3
no-trade-objective s = cong (λ X → Risk.objective X 0) (no-trade-loss s) ∙ D.objective-A

high-fee-no-trade-optimum : ∀ s → 4 ≤ᵣ s → ∀ w t →
  Risk.objective (netLoss s 1) 0 ≤ᵣ Risk.objective (netLoss s w) t
high-fee-no-trade-optimum s four≤s w t =
  isTrans≡≤ᵣ _ _ _ (no-trade-objective s) (high-fee-global-bound s four≤s w t)

-- Concrete linkage to the general portfolio and execution-cost model.
market : Market 2 4
market F.zero = D.assetA
market (F.suc F.zero) = D.assetB

initial : Vector 2
initial = two 1 0

holdings : ℝ → Vector 2
holdings w = two w (1 -ᵣ w)

rates : ℝ → Vector 2
rates s _ = s ·ᵣ D.half

rates-nonnegative : ∀ s → 0 ≤ᵣ s → ∀ i → 0 ≤ᵣ rates s i
rates-nonnegative s s₊ i = nonnegative-mul s D.half s₊ decℚ≤ᵣ?

holdings-total : ∀ w → sum (holdings w) ≡ 1
holdings-total w = ℝ!

holdings-loss : ∀ w → portfolioLoss market (holdings w) ≡ D.mixed w
holdings-loss w = funExt (λ i → ℝ!)

fee-implementation : ∀ s w → TC.transactionCost (rates s) initial (holdings w) ≡ fee s w
fee-implementation s w = cong₂
  (λ x y → (s ·ᵣ D.half) ·ᵣ x +ᵣ ((s ·ᵣ D.half) ·ᵣ y +ᵣ 0))
  (minusComm-absᵣ w 1) (cong absᵣ difference)
  ∙ ℝ!
  where
  difference : (1 -ᵣ w) -ᵣ 0 ≡ 1 -ᵣ w
  difference = ℝ!

netLoss-implementation : ∀ s w →
  TC.allInLoss market (rates s) initial (holdings w) ≡ netLoss s w
netLoss-implementation s w = funExt λ i →
  cong₂ _+ᵣ_ (fee-implementation s w) (funExt⁻ (holdings-loss w) i)

-- Numerical decisions use a modest fee s=1 and a high fee s=5. These are
-- abstract loss units; the fee thresholds are properties of this market.
cheap-target-CVaR : Risk.IsCVaR (netLoss 1 target) (rat [ 9 / 4 ])
cheap-target-CVaR = subst (Risk.IsCVaR (netLoss 1 target)) ℝ! (target-net-CVaR 1)

cheap-balanced-CVaR : Risk.IsCVaR (netLoss 1 D.half) (rat [ 5 / 2 ])
cheap-balanced-CVaR = subst (Risk.IsCVaR (netLoss 1 D.half)) ℝ! (balanced-net-CVaR 1)

expensive-target-CVaR : Risk.IsCVaR (netLoss 5 target) (rat [ 13 / 4 ])
expensive-target-CVaR = subst (Risk.IsCVaR (netLoss 5 target)) ℝ! (target-net-CVaR 5)

cheap-trade-optimal : ∀ w t → rat [ 9 / 4 ] ≤ᵣ Risk.objective (netLoss 1 w) t
cheap-trade-optimal w t = isTrans≡≤ᵣ _ _ _ ℝ!
  (low-fee-global-bound 1 decℚ≤ᵣ? decℚ≤ᵣ? w t)

expensive-hold-optimal : ∀ w t → 3 ≤ᵣ Risk.objective (netLoss 5 w) t
expensive-hold-optimal = high-fee-global-bound 5 decℚ≤ᵣ?

cheap-target-accepted : Risk.Accepted (netLoss 1 target) (rat [ 9 / 4 ])
cheap-target-accepted = Laws.CVaR-bound→accepted (netLoss 1 target) (rat [ 9 / 4 ])
  (rat [ 9 / 4 ]) cheap-target-CVaR (≤ᵣ-refl _)

cheap-full-rebalance-exceeds-budget :
  Risk.Accepted (netLoss 1 D.half) (rat [ 9 / 4 ]) → ⊥
cheap-full-rebalance-exceeds-budget accepted = isIrrefl<ᵣ (rat [ 5 / 2 ])
  (isTrans≤<ᵣ _ _ _
    (Laws.CVaR-accepted→bound (netLoss 1 D.half) (rat [ 5 / 2 ]) (rat [ 9 / 4 ])
      cheap-balanced-CVaR accepted) decℚ<ᵣ?)
