-- Methods: CVaR threshold/dual bounds and portfolio risk diversification.
-- See ../../REFERENCES.md#rockafellar-uryasev-2002, #shapiro-2016 and
-- #markowitz-1952. The four loss scenarios and 50% tail are synthetic;
-- the global optimality statements concern exactly this constructed market.

module Cubical.HITs.CauchyReals.Example.Financial.Examples.Portfolio.Diversification where

open import Cubical.HITs.CauchyReals.Example.Financial.Risk.ExpectedShortfall
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.Shortfall
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.WorstCase
open import Cubical.HITs.CauchyReals.Foundation.Rationals using ([_/_])
open import Cubical.Data.NatPlusOne using (fromNatℕ₊₁)
open import Cubical.Data.Int.Base using (fromNatℤ)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
import Cubical.Data.FinData.Base as F
import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.HITs.CauchyReals.Example.Financial.Examples.CommonScenarioData public
  using (four; half; quarter; equalProbability; halfTail)
  renaming (stress02 to dualA; stress12 to dualB; stress01 to dualBalanced;
    stress02-admissible to dualA-admissible; stress12-admissible to dualB-admissible;
    stress01-admissible to dualBalanced-admissible)

-- Four equally probable scenarios, in loss convention. The two assets
-- have different stress scenarios and the same expected loss.
module Risk = TailRisk equalProbability halfTail
open Risk

assetA assetB : Vector 4
assetA = four 6 -2 0 0
assetB = four -2 6 0 0

-- Every real w is allowed: short positions and leverage are included.
mixed : ℝ → Vector 4
mixed w i = w ·ᵣ assetA i +ᵣ (1 -ᵣ w) ·ᵣ assetB i

balanced : Vector 4
balanced = mixed half

balanced-values : balanced ≡ four 2 2 0 0
balanced-values = funExt λ
  { F.zero → ℝ!
  ; (F.suc F.zero) → ℝ!
  ; (F.suc (F.suc F.zero)) → ℝ!
  ; (F.suc (F.suc (F.suc F.zero))) → ℝ!
  }

mean-A : expectation equalProbability assetA ≡ 1
mean-A = ℝ!

mean-B : expectation equalProbability assetB ≡ 1
mean-B = ℝ!

mean-mixed : ∀ w → expectation equalProbability (mixed w) ≡ 1
mean-mixed w =
  expectation-add equalProbability (λ i → w ·ᵣ assetA i)
    (λ i → (1 -ᵣ w) ·ᵣ assetB i)
  ∙ cong₂ _+ᵣ_
      (expectation-scale equalProbability w assetA ∙ cong (w ·ᵣ_) mean-A)
      (expectation-scale equalProbability (1 -ᵣ w) assetB
        ∙ cong ((1 -ᵣ w) ·ᵣ_) mean-B)
  ∙ ℝ!

mean-balanced : expectation equalProbability balanced ≡ 1
mean-balanced = mean-mixed half


private
  stop-at-zero : ∀ x → 0 ≤ᵣ x → stopLoss x 0 ≡ x
  stop-at-zero = stopLoss-at-zero

  stops-A : ∀ i → stopLoss (assetA i) 0 ≡ four 6 0 0 0 i
  stops-A F.zero = stop-at-zero 6 decℚ≤ᵣ?
  stops-A (F.suc F.zero) = stopLoss-zero-below -2 0 decℚ≤ᵣ?
  stops-A (F.suc (F.suc F.zero)) = stop-at-zero 0 decℚ≤ᵣ?
  stops-A (F.suc (F.suc (F.suc F.zero))) = stop-at-zero 0 decℚ≤ᵣ?

  stops-B : ∀ i → stopLoss (assetB i) 0 ≡ four 0 6 0 0 i
  stops-B F.zero = stopLoss-zero-below -2 0 decℚ≤ᵣ?
  stops-B (F.suc F.zero) = stop-at-zero 6 decℚ≤ᵣ?
  stops-B (F.suc (F.suc F.zero)) = stop-at-zero 0 decℚ≤ᵣ?
  stops-B (F.suc (F.suc (F.suc F.zero))) = stop-at-zero 0 decℚ≤ᵣ?

  stops-balanced-values : ∀ i → stopLoss (four 2 2 0 0 i) 0 ≡ four 2 2 0 0 i
  stops-balanced-values F.zero = stop-at-zero 2 decℚ≤ᵣ?
  stops-balanced-values (F.suc F.zero) = stop-at-zero 2 decℚ≤ᵣ?
  stops-balanced-values (F.suc (F.suc F.zero)) = stop-at-zero 0 decℚ≤ᵣ?
  stops-balanced-values (F.suc (F.suc (F.suc F.zero))) = stop-at-zero 0 decℚ≤ᵣ?

objective-A : objective assetA 0 ≡ 3
objective-A =
  cong (λ X → 0 +ᵣ 2 ·ᵣ expectation equalProbability X) (funExt stops-A) ∙ ℝ!

objective-B : objective assetB 0 ≡ 3
objective-B =
  cong (λ X → 0 +ᵣ 2 ·ᵣ expectation equalProbability X) (funExt stops-B) ∙ ℝ!

objective-balanced : objective balanced 0 ≡ 2
objective-balanced =
  cong (λ X → objective X 0) balanced-values
  ∙ cong (λ X → 0 +ᵣ 2 ·ᵣ expectation equalProbability X)
      (funExt stops-balanced-values)
  ∙ ℝ!

dual-value-A : expectation dualA assetA ≡ 3
dual-value-A = ℝ!

dual-value-B : expectation dualB assetB ≡ 3
dual-value-B = ℝ!

-- The central hedge: this admissible dual measure values EVERY fully
-- invested portfolio at 2, independently of the real weight w.
dual-value-mixed : ∀ w → expectation dualBalanced (mixed w) ≡ 2
dual-value-mixed w = ℝ!

certificate-A : OptimalityCertificate assetA
certificate-A .threshold = 0
certificate-A .dual = dualA
certificate-A .dual-admissible = dualA-admissible
certificate-A .tight = objective-A ∙ sym dual-value-A

certificate-B : OptimalityCertificate assetB
certificate-B .threshold = 0
certificate-B .dual = dualB
certificate-B .dual-admissible = dualB-admissible
certificate-B .tight = objective-B ∙ sym dual-value-B

certificate-balanced : OptimalityCertificate balanced
certificate-balanced .threshold = 0
certificate-balanced .dual = dualBalanced
certificate-balanced .dual-admissible = dualBalanced-admissible
certificate-balanced .tight = objective-balanced ∙ sym (dual-value-mixed half)

CVaR-A : IsCVaR assetA 3
CVaR-A = subst (IsCVaR assetA) objective-A (certified-CVaR assetA certificate-A)

CVaR-B : IsCVaR assetB 3
CVaR-B = subst (IsCVaR assetB) objective-B (certified-CVaR assetB certificate-B)

CVaR-balanced : IsCVaR balanced 2
CVaR-balanced = subst (IsCVaR balanced) objective-balanced
  (certified-CVaR balanced certificate-balanced)

-- This proves joint global optimality over BOTH portfolio holdings and
-- the auxiliary threshold, not merely over a finite grid of trial weights.
all-portfolios-lower-bound : ∀ w t → 2 ≤ᵣ objective (mixed w) t
all-portfolios-lower-bound w t =
  isTrans≡≤ᵣ _ _ _ (sym (dual-value-mixed w))
    (weak-duality (mixed w) dualBalanced dualBalanced-admissible t)

balanced-global-optimum : ∀ w t → objective balanced 0 ≤ᵣ objective (mixed w) t
balanced-global-optimum w t =
  isTrans≡≤ᵣ _ _ _ objective-balanced (all-portfolios-lower-bound w t)

budget-two-accepted : Accepted balanced 2
budget-two-accepted = PT.∣ 0 , ≡ᵣWeaken≤ᵣ _ _ objective-balanced ∣₁

tail-risk-strict-improvement : objective balanced 0 <ᵣ objective assetA 0
tail-risk-strict-improvement = subst2 _<ᵣ_
  (sym objective-balanced) (sym objective-A) decℚ<ᵣ?

tail-risk-strict-improvement-B : objective balanced 0 <ᵣ objective assetB 0
tail-risk-strict-improvement-B = subst2 _<ᵣ_
  (sym objective-balanced) (sym objective-B) decℚ<ᵣ?

worst-A : worstCase assetA ≡ 6
worst-A = isAntisym≤ᵣ _ _ (worstCase-least assetA 6 upper)
  (worstCase-upper assetA F.zero)
  where
  upper : ∀ i → assetA i ≤ᵣ 6
  upper F.zero = decℚ≤ᵣ?
  upper (F.suc F.zero) = decℚ≤ᵣ?
  upper (F.suc (F.suc F.zero)) = decℚ≤ᵣ?
  upper (F.suc (F.suc (F.suc F.zero))) = decℚ≤ᵣ?

worst-B : worstCase assetB ≡ 6
worst-B = isAntisym≤ᵣ _ _ (worstCase-least assetB 6 upper)
  (worstCase-upper assetB (F.suc F.zero))
  where
  upper : ∀ i → assetB i ≤ᵣ 6
  upper F.zero = decℚ≤ᵣ?
  upper (F.suc F.zero) = decℚ≤ᵣ?
  upper (F.suc (F.suc F.zero)) = decℚ≤ᵣ?
  upper (F.suc (F.suc (F.suc F.zero))) = decℚ≤ᵣ?

worst-balanced : worstCase balanced ≡ 2
worst-balanced = cong worstCase balanced-values
  ∙ isAntisym≤ᵣ _ _ (worstCase-least (four 2 2 0 0) 2 upper)
      (worstCase-upper (four 2 2 0 0) F.zero)
  where
  upper : ∀ i → four 2 2 0 0 i ≤ᵣ 2
  upper F.zero = decℚ≤ᵣ?
  upper (F.suc F.zero) = decℚ≤ᵣ?
  upper (F.suc (F.suc F.zero)) = decℚ≤ᵣ?
  upper (F.suc (F.suc (F.suc F.zero))) = decℚ≤ᵣ?

-- The same explicit dual measure certifies global stress minimization.
-- It is a probability measure, so its expectation cannot exceed the max.
all-portfolios-worst-lower-bound : ∀ w → 2 ≤ᵣ worstCase (mixed w)
all-portfolios-worst-lower-bound w =
  isTrans≡≤ᵣ _ _ _ (sym (dual-value-mixed w))
    (isTrans≤≡ᵣ _ _ _
      (expectation-monotone dualBalanced (mixed w)
        (λ _ → worstCase (mixed w)) (worstCase-upper (mixed w)))
      (expectation-constant dualBalanced (worstCase (mixed w))))

balanced-global-stress-optimum : ∀ w → worstCase balanced ≤ᵣ worstCase (mixed w)
balanced-global-stress-optimum w =
  isTrans≡≤ᵣ _ _ _ worst-balanced (all-portfolios-worst-lower-bound w)

stress-risk-strict-improvement : worstCase balanced <ᵣ worstCase assetA
stress-risk-strict-improvement = subst2 _<ᵣ_
  (sym worst-balanced) (sym worst-A) decℚ<ᵣ?

stress-risk-strict-improvement-B : worstCase balanced <ᵣ worstCase assetB
stress-risk-strict-improvement-B = subst2 _<ᵣ_
  (sym worst-balanced) (sym worst-B) decℚ<ᵣ?

stress-budget-two : worstCase balanced ≤ᵣ 2
stress-budget-two = ≡ᵣWeaken≤ᵣ _ _ worst-balanced

-- A tight stress budget fixes the allocation uniquely, even with shorting
-- permitted. These affine recovery identities avoid division by a variable.
stress-budget-unique : ∀ w → worstCase (mixed w) ≤ᵣ 2 → w ≡ half
stress-budget-unique w bound = isAntisym≤ᵣ w half weight-upper weight-lower
  where
  eighth : ℝ
  eighth = rat [ 1 / 8 ]

  first-bound : mixed w F.zero ≤ᵣ 2
  first-bound = isTrans≤ᵣ _ _ _ (worstCase-upper (mixed w) F.zero) bound

  second-bound : mixed w (F.suc F.zero) ≤ᵣ 2
  second-bound =
    isTrans≤ᵣ _ _ _ (worstCase-upper (mixed w) (F.suc F.zero)) bound

  recover-first : eighth ·ᵣ (mixed w F.zero +ᵣ 2) ≡ w
  recover-first = ℝ!

  recover-second : eighth ·ᵣ (6 -ᵣ mixed w (F.suc F.zero)) ≡ w
  recover-second = ℝ!

  first-endpoint : eighth ·ᵣ (2 +ᵣ 2) ≡ half
  first-endpoint = ℝ!

  second-endpoint : eighth ·ᵣ (6 -ᵣ 2) ≡ half
  second-endpoint = ℝ!

  weight-upper : w ≤ᵣ half
  weight-upper = subst2 _≤ᵣ_ recover-first first-endpoint
    (≤ᵣ-o·ᵣ _ _ eighth decℚ≤ᵣ? (≤ᵣ-+o _ _ 2 first-bound))

  weight-lower : half ≤ᵣ w
  weight-lower = subst2 _≤ᵣ_ second-endpoint recover-second
    (≤ᵣ-o·ᵣ _ _ eighth decℚ≤ᵣ?
      (≤ᵣ-o+ _ _ 6 (-ᵣ≤ᵣ _ _ second-bound)))

-- Tail-risk minimizers need not be unique. A different allocation has the
-- same CVaR 2, but incurs stress loss 4. Combining the two budgets matters.
quarter-values : mixed quarter ≡ four 0 4 0 0
quarter-values = funExt λ
  { F.zero → ℝ!
  ; (F.suc F.zero) → ℝ!
  ; (F.suc (F.suc F.zero)) → ℝ!
  ; (F.suc (F.suc (F.suc F.zero))) → ℝ!
  }

quarter≢half : (quarter ≡ half) → ⊥
quarter≢half p = isAsym<ᵣ quarter half decℚ<ᵣ?
  (subst2 _<ᵣ_ p (sym p) decℚ<ᵣ?)

objective-quarter : objective (mixed quarter) 0 ≡ 2
objective-quarter = cong (λ X → objective X 0) quarter-values
  ∙ cong (λ X → 0 +ᵣ 2 ·ᵣ expectation equalProbability X) (funExt stops)
  ∙ ℝ!
  where
  stops : ∀ i → stopLoss (four 0 4 0 0 i) 0 ≡ four 0 4 0 0 i
  stops F.zero = stop-at-zero 0 decℚ≤ᵣ?
  stops (F.suc F.zero) = stop-at-zero 4 decℚ≤ᵣ?
  stops (F.suc (F.suc F.zero)) = stop-at-zero 0 decℚ≤ᵣ?
  stops (F.suc (F.suc (F.suc F.zero))) = stop-at-zero 0 decℚ≤ᵣ?

certificate-quarter : OptimalityCertificate (mixed quarter)
certificate-quarter .threshold = 0
certificate-quarter .dual = dualBalanced
certificate-quarter .dual-admissible = dualBalanced-admissible
certificate-quarter .tight = objective-quarter ∙ sym (dual-value-mixed quarter)

CVaR-quarter : IsCVaR (mixed quarter) 2
CVaR-quarter = subst (IsCVaR (mixed quarter)) objective-quarter
  (certified-CVaR (mixed quarter) certificate-quarter)

worst-quarter : worstCase (mixed quarter) ≡ 4
worst-quarter = cong worstCase quarter-values
  ∙ isAntisym≤ᵣ _ _ (worstCase-least (four 0 4 0 0) 4 upper)
      (worstCase-upper (four 0 4 0 0) (F.suc F.zero))
  where
  upper : ∀ i → four 0 4 0 0 i ≤ᵣ 4
  upper F.zero = decℚ≤ᵣ?
  upper (F.suc F.zero) = decℚ≤ᵣ?
  upper (F.suc (F.suc F.zero)) = decℚ≤ᵣ?
  upper (F.suc (F.suc (F.suc F.zero))) = decℚ≤ᵣ?
