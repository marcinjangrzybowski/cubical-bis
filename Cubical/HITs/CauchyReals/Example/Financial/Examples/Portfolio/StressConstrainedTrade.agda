-- Methods: proportional trading costs, CVaR optimization and robust constraints.
-- See ../../REFERENCES.md#boyd-2017, #rockafellar-uryasev-2002 and
-- #ben-tal-nemirovski-1998. The cap applies to raw scenario loss; net CVaR
-- includes execution fees. The cap range [2,4] and numerical fee are synthetic.

module Cubical.HITs.CauchyReals.Example.Financial.Examples.Portfolio.StressConstrainedTrade where

open import Cubical.HITs.CauchyReals.Example.Financial.Portfolio.Base
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.RiskLaws
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.Shortfall
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.WorstCase
open import Cubical.HITs.CauchyReals.Example.Financial.Portfolio.TransactionCosts using (cash-worstCase)
open import Cubical.HITs.CauchyReals.Algebra.Order.AbsoluteValue
open import Cubical.HITs.CauchyReals.Algebra.Order.Lattice using (≤maxᵣ)
open import Cubical.HITs.CauchyReals.Algebra.Order.Addition.Properties using (x≤y→0≤y-x)
open import Cubical.HITs.CauchyReals.Algebra.Order.Properties using (isIrrefl<ᵣ)
open import Cubical.HITs.CauchyReals.Foundation.Rationals using ([_/_])
open import Cubical.Data.NatPlusOne using (fromNatℕ₊₁)
open import Cubical.Data.Int.Base using (fromNatℤ)
open import Cubical.Data.Empty using (⊥; isProp⊥)
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
import Cubical.HITs.CauchyReals.Example.Financial.Examples.Portfolio.Diversification as D
import Cubical.HITs.CauchyReals.Example.Financial.Examples.Portfolio.Rebalancing as R
import Cubical.Data.FinData.Base as F
import Cubical.HITs.PropositionalTruncation as PT

module Risk = TailRisk D.equalProbability D.halfTail
module Laws = CVaRLaws D.equalProbability D.halfTail

private
  eighth : ℝ
  eighth = rat [ 1 / 8 ]

-- Minimize net CVaR from the initial holding (1,0), subject to a bound c
-- on RAW scenario loss. Execution fees are additional deterministic losses;
-- the separately reported NET stress value includes that additional fee.
capWeight : ℝ → ℝ
capWeight c = (c +ᵣ 2) ·ᵣ eighth

capFee : ℝ → ℝ → ℝ
capFee s c = s ·ᵣ ((6 -ᵣ c) ·ᵣ eighth)

capValue : ℝ → ℝ → ℝ
capValue s c = 2 +ᵣ capFee s c

capWeight-nonnegative : ∀ c → 2 ≤ᵣ c → 0 ≤ᵣ capWeight c
capWeight-nonnegative c two≤c = nonnegative-mul (c +ᵣ 2) eighth
  (nonnegative-add c 2 (isTrans≤ᵣ 0 2 c decℚ≤ᵣ? two≤c) decℚ≤ᵣ?) decℚ≤ᵣ?

capWeight-at-most-one : ∀ c → c ≤ᵣ 4 → capWeight c ≤ᵣ 1
capWeight-at-most-one c c≤four = isTrans≤≡ᵣ _ _ _
  (≤ᵣ-·ᵣo _ _ eighth decℚ≤ᵣ?
    (≤ᵣ-+o c 6 2 (isTrans≤ᵣ c 4 6 c≤four decℚ≤ᵣ?))) endpoint
  where
  endpoint : (6 +ᵣ 2) ·ᵣ eighth ≡ 1
  endpoint = ℝ!

capAllocation : ∀ c → 2 ≤ᵣ c → c ≤ᵣ 4 → Allocation 2
capAllocation c two≤c c≤four = R.holdings (capWeight c) , nonnegative ,
  R.holdings-total (capWeight c)
  where
  nonnegative : ∀ i → 0 ≤ᵣ R.holdings (capWeight c) i
  nonnegative F.zero = capWeight-nonnegative c two≤c
  nonnegative (F.suc F.zero) = x≤y→0≤y-x (capWeight c) 1 (capWeight-at-most-one c c≤four)

cap-losses : ∀ c → D.mixed (capWeight c) ≡ D.four c (4 -ᵣ c) 0 0
cap-losses c = funExt λ
  { F.zero → ℝ!
  ; (F.suc F.zero) → ℝ!
  ; (F.suc (F.suc F.zero)) → ℝ!
  ; (F.suc (F.suc (F.suc F.zero))) → ℝ!
  }

raw-objective : ∀ c → 2 ≤ᵣ c → c ≤ᵣ 4 → Risk.objective (D.mixed (capWeight c)) 0 ≡ 2
raw-objective c two≤c c≤four = cong (λ X → Risk.objective X 0) (cap-losses c)
  ∙ cong (λ X → 0 +ᵣ 2 ·ᵣ expectation D.equalProbability X) (funExt stops)
  ∙ ℝ!
  where
  stops : ∀ i → stopLoss (D.four c (4 -ᵣ c) 0 0 i) 0 ≡ D.four c (4 -ᵣ c) 0 0 i
  stops F.zero = stopLoss-at-zero c (isTrans≤ᵣ 0 2 c decℚ≤ᵣ? two≤c)
  stops (F.suc F.zero) = stopLoss-at-zero (4 -ᵣ c) (x≤y→0≤y-x c 4 c≤four)
  stops (F.suc (F.suc F.zero)) = stopLoss-at-zero 0 (≤ᵣ-refl 0)
  stops (F.suc (F.suc (F.suc F.zero))) = stopLoss-at-zero 0 (≤ᵣ-refl 0)

raw-CVaR : ∀ c → 2 ≤ᵣ c → c ≤ᵣ 4 → Risk.IsCVaR (D.mixed (capWeight c)) 2
raw-CVaR c two≤c c≤four = D.all-portfolios-lower-bound (capWeight c) ,
  PT.∣ 0 , raw-objective c two≤c c≤four ∣₁

raw-stress : ∀ c → 2 ≤ᵣ c → worstCase (D.mixed (capWeight c)) ≡ c
raw-stress c two≤c = cong worstCase (cap-losses c)
  ∙ worstCase-exact-at (D.four c (4 -ᵣ c) 0 0) c F.zero bound refl
  where
  endpoint : 4 -ᵣ 2 ≡ 2
  endpoint = ℝ!

  bound : ∀ i → D.four c (4 -ᵣ c) 0 0 i ≤ᵣ c
  bound F.zero = ≤ᵣ-refl c
  bound (F.suc F.zero) = isTrans≤ᵣ _ 2 c
    (isTrans≤≡ᵣ _ _ _ (≤ᵣ-o+ _ _ 4 (-ᵣ≤ᵣ 2 c two≤c)) endpoint) two≤c
  bound (F.suc (F.suc F.zero)) = isTrans≤ᵣ 0 2 c decℚ≤ᵣ? two≤c
  bound (F.suc (F.suc (F.suc F.zero))) = isTrans≤ᵣ 0 2 c decℚ≤ᵣ? two≤c

cap-fee-exact : ∀ s c → c ≤ᵣ 4 → R.fee s (capWeight c) ≡ capFee s c
cap-fee-exact s c c≤four = cong (s ·ᵣ_)
  (absᵣNonNeg (1 -ᵣ capWeight c)
    (x≤y→0≤y-x (capWeight c) 1 (capWeight-at-most-one c c≤four))
    ∙ difference)
  where
  difference : 1 -ᵣ capWeight c ≡ (6 -ᵣ c) ·ᵣ eighth
  difference = ℝ!

net-CVaR : ∀ s c → 2 ≤ᵣ c → c ≤ᵣ 4 →
  Risk.IsCVaR (R.netLoss s (capWeight c)) (capValue s c)
net-CVaR s c two≤c c≤four = subst (Risk.IsCVaR (R.netLoss s (capWeight c)))
  (cong (_+ᵣ 2) (cap-fee-exact s c c≤four) ∙ +ᵣComm _ 2)
  (Laws.IsCVaR-cash (D.mixed (capWeight c)) 2 (R.fee s (capWeight c))
    (raw-CVaR c two≤c c≤four))

net-stress : ∀ s c → 2 ≤ᵣ c → c ≤ᵣ 4 →
  worstCase (R.netLoss s (capWeight c)) ≡ c +ᵣ capFee s c
net-stress s c two≤c c≤four = cash-worstCase (D.mixed (capWeight c)) (R.fee s (capWeight c))
  ∙ cong₂ _+ᵣ_ (cap-fee-exact s c c≤four) (raw-stress c two≤c)
  ∙ +ᵣComm _ c

-- The first stress scenario alone bounds the weight of asset A.
stress-bounds-weight : ∀ c w → worstCase (D.mixed w) ≤ᵣ c → w ≤ᵣ capWeight c
stress-bounds-weight c w stress = subst2 _≤ᵣ_ recover endpoint
  (≤ᵣ-o·ᵣ _ _ eighth decℚ≤ᵣ?
    (≤ᵣ-+o _ _ 2 (isTrans≤ᵣ _ _ _ (worstCase-upper (D.mixed w) F.zero) stress)))
  where
  recover : eighth ·ᵣ (D.mixed w F.zero +ᵣ 2) ≡ w
  recover = ℝ!
  endpoint : eighth ·ᵣ (c +ᵣ 2) ≡ capWeight c
  endpoint = ℝ!

constrained-fee-lower : ∀ s c w → 0 ≤ᵣ s → worstCase (D.mixed w) ≤ᵣ c →
  capFee s c ≤ᵣ R.fee s w
constrained-fee-lower s c w s₊ stress = isTrans≡≤ᵣ _ _ _ expansion
  (≤ᵣ-o·ᵣ _ _ s s₊
    (isTrans≤ᵣ _ _ _
      (≤ᵣ-o+ _ _ 1 (-ᵣ≤ᵣ w (capWeight c) (stress-bounds-weight c w stress)))
      (isTrans≤≡ᵣ _ _ _ (≤maxᵣ (1 -ᵣ w) (-ᵣ (1 -ᵣ w))) (sym (abs-max (1 -ᵣ w))))))
  where
  expansion : capFee s c ≡ s ·ᵣ (1 -ᵣ capWeight c)
  expansion = ℝ!

-- Every signed real competitor is allowed, provided its RAW stress obeys
-- the cap. The fee level can be arbitrarily large, but must be nonnegative.
constrained-global-bound : ∀ s c → 0 ≤ᵣ s → ∀ w t →
  worstCase (D.mixed w) ≤ᵣ c → capValue s c ≤ᵣ Risk.objective (R.netLoss s w) t
constrained-global-bound s c s₊ w t stress = isTrans≡≤ᵣ _ _ _ (+ᵣComm 2 (capFee s c))
  (isTrans≤≡ᵣ _ _ _
    (≤ᵣMonotone+ᵣ _ _ _ _ (constrained-fee-lower s c w s₊ stress)
      (D.all-portfolios-lower-bound w (t -ᵣ R.fee s w)))
    (sym (R.net-objective s w t)))

-- Bundle feasibility, attained net CVaR, and comparison with every feasible
-- competitor. This makes the optimization domain part of the certificate.
IsConstrainedOptimum : ℝ → ℝ → ℝ → ℝ → Type₀
IsConstrainedOptimum s c w value = (worstCase (D.mixed w) ≤ᵣ c) ×
  Risk.IsCVaR (R.netLoss s w) value ×
  (∀ v t → worstCase (D.mixed v) ≤ᵣ c → value ≤ᵣ Risk.objective (R.netLoss s v) t)

constrained-optimal : ∀ s c → 0 ≤ᵣ s → 2 ≤ᵣ c → c ≤ᵣ 4 →
  IsConstrainedOptimum s c (capWeight c) (capValue s c)
constrained-optimal s c s₊ two≤c c≤four =
  ≡ᵣWeaken≤ᵣ _ _ (raw-stress c two≤c) ,
  net-CVaR s c two≤c c≤four , constrained-global-bound s c s₊

-- Even high fees cannot make holding the initial asset feasible under
-- these raw stress caps: its stress loss is 6 before any execution fee.
no-trade-infeasible : ∀ c → c ≤ᵣ 4 → worstCase (D.mixed 1) ≤ᵣ c → ⊥
no-trade-infeasible c c≤four stress = isIrrefl<ᵣ 6
  (isTrans≤<ᵣ _ 4 _
    (isTrans≤ᵣ 6 c 4 (isTrans≡≤ᵣ _ _ _ (sym initial-stress) stress) c≤four)
    decℚ<ᵣ?)
  where
  initial-loss : D.mixed 1 ≡ D.assetA
  initial-loss = funExt (λ i → ℝ!)
  initial-stress : worstCase (D.mixed 1) ≡ 6
  initial-stress = cong worstCase initial-loss ∙ D.worst-A

-- With fee 1 and raw stress cap 3, trade to (5/8,3/8).
example-weight : capWeight 3 ≡ rat [ 5 / 8 ]
example-weight = ℝ!

example-raw-stress : worstCase (D.mixed (capWeight 3)) ≡ 3
example-raw-stress = raw-stress 3 decℚ≤ᵣ?

example-net-stress : worstCase (R.netLoss 1 (capWeight 3)) ≡ rat [ 27 / 8 ]
example-net-stress = net-stress 1 3 decℚ≤ᵣ? decℚ≤ᵣ? ∙ ℝ!

example-CVaR : Risk.IsCVaR (R.netLoss 1 (capWeight 3)) (rat [ 19 / 8 ])
example-CVaR = subst (Risk.IsCVaR (R.netLoss 1 (capWeight 3))) ℝ!
  (net-CVaR 1 3 decℚ≤ᵣ? decℚ≤ᵣ?)

example-budget-accepted : Risk.Accepted (R.netLoss 1 (capWeight 3)) (rat [ 19 / 8 ])
example-budget-accepted = Laws.CVaR-bound→accepted (R.netLoss 1 (capWeight 3))
  (rat [ 19 / 8 ]) (rat [ 19 / 8 ]) example-CVaR (≤ᵣ-refl _)

-- The lower budget 9/4 is feasible without the raw stress constraint, but
-- is impossible for EVERY portfolio satisfying raw stress ≤ 3.
example-lower-budget-impossible : ∀ w → worstCase (D.mixed w) ≤ᵣ 3 →
  Risk.Accepted (R.netLoss 1 w) (rat [ 9 / 4 ]) → ⊥
example-lower-budget-impossible w stress = PT.rec isProp⊥ λ (t , bound) →
  isIrrefl<ᵣ (rat [ 19 / 8 ])
    (isTrans≤<ᵣ _ _ _
      (isTrans≤ᵣ _ _ _
        (isTrans≡≤ᵣ _ _ _ value (constrained-global-bound 1 3 decℚ≤ᵣ? w t stress))
        bound)
      decℚ<ᵣ?)
  where
  value : rat [ 19 / 8 ] ≡ capValue 1 3
  value = ℝ!
