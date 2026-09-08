-- Worst expectations over specified probability models motivate this example:
-- ../../REFERENCES.md#ben-tal-nemirovski-1998 and #shapiro-2016.
-- The two model laws are synthetic. The mixture guarantees range over their
-- convex hull, not arbitrary probability laws outside the supplied generators.

module Cubical.HITs.CauchyReals.Example.Financial.Examples.Portfolio.RobustAllocation where

open import Cubical.HITs.CauchyReals.Example.Financial.Risk.Ambiguity
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.WorstCase
open import Cubical.HITs.CauchyReals.Algebra.Order.Properties using (isIrrefl<ᵣ)
open import Cubical.Data.Empty using (⊥)
open import Cubical.HITs.CauchyReals.Foundation.Rationals using ([_/_])
open import Cubical.Data.NatPlusOne using (fromNatℕ₊₁)
open import Cubical.Data.Int.Base using (fromNatℤ)
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
open import Cubical.Foundations.Equiv using (equivFun)
import Cubical.HITs.CauchyReals.Example.Financial.Examples.Portfolio.Diversification as D
import Cubical.Data.FinData.Base as F

-- Two alternative scenario laws for the SAME asset losses. Their entire
-- convex hull, with arbitrary real model weights, is the ambiguity set.
upModel downModel : Distribution 4
upModel = D.four D.half D.quarter D.quarter 0 , nonnegative , total
  where
  nonnegative : ∀ i → 0 ≤ᵣ D.four D.half D.quarter D.quarter 0 i
  nonnegative F.zero = decℚ≤ᵣ?
  nonnegative (F.suc F.zero) = decℚ≤ᵣ?
  nonnegative (F.suc (F.suc F.zero)) = decℚ≤ᵣ?
  nonnegative (F.suc (F.suc (F.suc F.zero))) = decℚ≤ᵣ?
  total : sum (D.four D.half D.quarter D.quarter 0) ≡ 1
  total = ℝ!
downModel = D.four (rat [ 1 / 8 ]) D.half (rat [ 3 / 8 ]) 0 , nonnegative , total
  where
  nonnegative : ∀ i → 0 ≤ᵣ D.four (rat [ 1 / 8 ]) D.half (rat [ 3 / 8 ]) 0 i
  nonnegative F.zero = decℚ≤ᵣ?
  nonnegative (F.suc F.zero) = decℚ≤ᵣ?
  nonnegative (F.suc (F.suc F.zero)) = decℚ≤ᵣ?
  nonnegative (F.suc (F.suc (F.suc F.zero))) = decℚ≤ᵣ?
  total : sum (D.four (rat [ 1 / 8 ]) D.half (rat [ 3 / 8 ]) 0) ≡ 1
  total = ℝ!

models : Fin 2 → Distribution 4
models F.zero = upModel
models (F.suc F.zero) = downModel

allocation : ℝ
allocation = rat [ 9 / 20 ]

capital : ℝ
capital = rat [ 7 / 5 ]

-- A fixed adversarial mixture supplies a global supporting bound.
modelWeights : Distribution 2
modelWeights = weights , nonnegative , total
  where
  weights : Vector 2
  weights F.zero = rat [ 3 / 5 ]
  weights (F.suc F.zero) = rat [ 2 / 5 ]
  nonnegative : ∀ i → 0 ≤ᵣ weights i
  nonnegative F.zero = decℚ≤ᵣ?
  nonnegative (F.suc F.zero) = decℚ≤ᵣ?
  total : sum weights ≡ 1
  total = ℝ!

up-mean : ∀ w → expectation upModel (D.mixed w) ≡ D.half +ᵣ 2 ·ᵣ w
up-mean w = ℝ!

down-mean : ∀ w → expectation downModel (D.mixed w) ≡ rat [ 11 / 4 ] -ᵣ 3 ·ᵣ w
down-mean w = ℝ!

adversarial-mean : ∀ w → expectation (mixture modelWeights models) (D.mixed w) ≡ capital
adversarial-mean w = expectation-mixture modelWeights models (D.mixed w)
  ∙ ℝ!

global-lower-bound : ∀ w → capital ≤ᵣ robustExpectation models (D.mixed w)
global-lower-bound w = isTrans≡≤ᵣ _ _ _ (sym (adversarial-mean w))
  (robust-mixture-upper models (D.mixed w) modelWeights)

allocation-model-values : ∀ i → expectation (models i) (D.mixed allocation) ≡ capital
allocation-model-values F.zero = up-mean allocation ∙ ℝ!
allocation-model-values (F.suc F.zero) = down-mean allocation ∙ ℝ!

allocation-risk : robustExpectation models (D.mixed allocation) ≡ capital
allocation-risk = isAntisym≤ᵣ _ _
  (robust-least models (D.mixed allocation) capital
    (λ i → ≡ᵣWeaken≤ᵣ _ _ (allocation-model-values i)))
  (global-lower-bound allocation)

global-optimum : ∀ w → robustExpectation models (D.mixed allocation)
  ≤ᵣ robustExpectation models (D.mixed w)
global-optimum w = isTrans≡≤ᵣ _ _ _ allocation-risk (global-lower-bound w)

-- An infinite family of real mixtures is certified by two model checks.
safe-under-every-mixture : (W : Distribution 2) →
  expectation (mixture W models) (D.mixed allocation) ≤ᵣ capital
safe-under-every-mixture = models-bound→mixtures models (D.mixed allocation) capital
  (λ i → ≡ᵣWeaken≤ᵣ _ _ (allocation-model-values i))

-- This version also permits finite selections of the original model labels,
-- including repetitions and changes of their enumeration.
safe-under-every-finite-mixture : AllFiniteMixturesBound models (D.mixed allocation) capital
safe-under-every-finite-mixture = equivFun
  (robust-budget≃finite-mixtures models (D.mixed allocation) capital)
  (≡ᵣWeaken≤ᵣ _ _ allocation-risk)

balanced-risk : robustExpectation models D.balanced ≡ rat [ 3 / 2 ]
balanced-risk = isAntisym≤ᵣ _ _
  (robust-least models D.balanced _ upper)
  (isTrans≡≤ᵣ _ _ _ (sym value-up) (robust-upper models D.balanced F.zero))
  where
  value-up : expectation upModel D.balanced ≡ rat [ 3 / 2 ]
  value-up = ℝ!
  value-down : expectation downModel D.balanced ≡ rat [ 5 / 4 ]
  value-down = ℝ!
  upper : ∀ i → expectation (models i) D.balanced ≤ᵣ rat [ 3 / 2 ]
  upper F.zero = ≡ᵣWeaken≤ᵣ _ _ value-up
  upper (F.suc F.zero) = isTrans≡≤ᵣ _ _ _ value-down decℚ≤ᵣ?

improves-on-equal-weights :
  robustExpectation models (D.mixed allocation) <ᵣ robustExpectation models D.balanced
improves-on-equal-weights = subst2 _<ᵣ_ (sym allocation-risk) (sym balanced-risk) decℚ<ᵣ?

-- Expected loss under the old nominal law remains 1 for every allocation;
-- ambiguity supplies information that the nominal mean criterion lacks.
nominal-mean-unchanged : expectation D.equalProbability (D.mixed allocation) ≡ 1
nominal-mean-unchanged = D.mean-mixed allocation

-- Tight ambiguous-mean capital determines the real weight uniquely.
allocation-unique : ∀ w → robustExpectation models (D.mixed w) ≤ᵣ capital → w ≡ allocation
allocation-unique w bound = isAntisym≤ᵣ _ _ weight-upper weight-lower
  where
  upper-model : D.half +ᵣ 2 ·ᵣ w ≤ᵣ capital
  upper-model = isTrans≡≤ᵣ _ _ _ (sym (up-mean w))
    (isTrans≤ᵣ _ _ _ (robust-upper models (D.mixed w) F.zero) bound)
  lower-model : rat [ 11 / 4 ] -ᵣ 3 ·ᵣ w ≤ᵣ capital
  lower-model = isTrans≡≤ᵣ _ _ _ (sym (down-mean w))
    (isTrans≤ᵣ _ _ _ (robust-upper models (D.mixed w) (F.suc F.zero)) bound)
  recover-upper : D.half ·ᵣ ((D.half +ᵣ 2 ·ᵣ w) -ᵣ D.half) ≡ w
  recover-upper = ℝ!
  upper-endpoint : D.half ·ᵣ (capital -ᵣ D.half) ≡ allocation
  upper-endpoint = ℝ!
  weight-upper : w ≤ᵣ allocation
  weight-upper = subst2 _≤ᵣ_ recover-upper upper-endpoint
    (≤ᵣ-o·ᵣ _ _ D.half decℚ≤ᵣ? (≤ᵣ-+o _ _ (-ᵣ D.half) upper-model))
  recover-lower : rat [ 1 / 3 ] ·ᵣ (rat [ 11 / 4 ] -ᵣ (rat [ 11 / 4 ] -ᵣ 3 ·ᵣ w)) ≡ w
  recover-lower = ℝ!
  lower-endpoint : rat [ 1 / 3 ] ·ᵣ (rat [ 11 / 4 ] -ᵣ capital) ≡ allocation
  lower-endpoint = ℝ!
  weight-lower : allocation ≤ᵣ w
  weight-lower = subst2 _≤ᵣ_ lower-endpoint recover-lower
    (≤ᵣ-o·ᵣ _ _ (rat [ 1 / 3 ]) decℚ≤ᵣ?
      (≤ᵣ-o+ _ _ (rat [ 11 / 4 ]) (-ᵣ≤ᵣ _ _ lower-model)))

balanced-exceeds-ambiguity-budget : robustExpectation models D.balanced ≤ᵣ capital → ⊥
balanced-exceeds-ambiguity-budget bound = isIrrefl<ᵣ (rat [ 3 / 2 ])
  (isTrans≤<ᵣ _ _ _ (isTrans≡≤ᵣ _ _ _ (sym balanced-risk) bound) decℚ<ᵣ?)

allocation-losses : D.mixed allocation ≡ D.four (rat [ 8 / 5 ]) (rat [ 12 / 5 ]) 0 0
allocation-losses = funExt λ
  { F.zero → ℝ!
  ; (F.suc F.zero) → ℝ!
  ; (F.suc (F.suc F.zero)) → ℝ!
  ; (F.suc (F.suc (F.suc F.zero))) → ℝ!
  }

allocation-stress : worstCase (D.mixed allocation) ≡ rat [ 12 / 5 ]
allocation-stress = cong worstCase allocation-losses
  ∙ isAntisym≤ᵣ _ _ (worstCase-least losses (rat [ 12 / 5 ]) upper)
    (worstCase-upper losses (F.suc F.zero))
  where
  losses : Vector 4
  losses = D.four (rat [ 8 / 5 ]) (rat [ 12 / 5 ]) 0 0
  upper : ∀ i → losses i ≤ᵣ rat [ 12 / 5 ]
  upper F.zero = decℚ≤ᵣ?
  upper (F.suc F.zero) = decℚ≤ᵣ?
  upper (F.suc (F.suc F.zero)) = decℚ≤ᵣ?
  upper (F.suc (F.suc (F.suc F.zero))) = decℚ≤ᵣ?

-- There is a real tradeoff: improving ambiguous mean risk worsens the
-- maximum loss relative to the previous equal-weight stress optimizer.
stress-tradeoff : worstCase D.balanced <ᵣ worstCase (D.mixed allocation)
stress-tradeoff = subst2 _<ᵣ_ (sym D.worst-balanced) (sym allocation-stress) decℚ<ᵣ?
