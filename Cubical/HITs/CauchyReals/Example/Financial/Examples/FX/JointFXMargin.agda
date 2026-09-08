-- Universal uncertainty-set constraints and stressed collateral motivate this
-- example: ../../REFERENCES.md#ben-tal-nemirovski-1998 and
-- #bcbs-iosco-margin-2020. The real box and 20% haircut are synthetic.
-- The whole-box proofs establish exact model-specific calls; two attaining
-- quotes alone would not establish universal coverage or regulatory compliance.

module Cubical.HITs.CauchyReals.Example.Financial.Examples.FX.JointFXMargin where

import Cubical.HITs.CauchyReals.Example.Financial.Examples.FX.JointMoveExample as JointMoveExample

open import Cubical.HITs.CauchyReals.Example.Financial.Instruments.FXBounds
open import Cubical.HITs.CauchyReals.Example.Financial.Margin.MarginControl
import Cubical.HITs.CauchyReals.Example.Financial.Margin.Scenario as Scenario
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.WorstCase
open import Cubical.HITs.CauchyReals.Foundation.Rationals using (ℚ; module ℚ; [_/_]; fromNatℚ)
open import Cubical.Data.NatPlusOne using (fromNatℕ₊₁)
open import Cubical.Data.Int.Base using (fromNatℤ)
open import Cubical.Data.Empty using (⊥)
open import Cubical.HITs.CauchyReals.Algebra.Order.Properties using (isIrrefl<ᵣ)
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
import Cubical.Data.Nat.Order as N
import Cubical.Data.FinData.Base as F
import Cubical.HITs.CauchyReals.Example.Financial.Examples.FX.BrokerMargin as B

-- The same two-swap portfolios have total foreign principal +100/-100.
-- Their cashflow aggregation permits this common-date valuation identity.
aggregateSwap : FXSwap
aggregateSwap = fx-swap 100 1 1 decℚ<ᵣ? decℚ<ᵣ? 0 30 N.zero-<-suc

claimAtA claimAtB : FXState → ℝ
claimAtA state = farValue aggregateSwap state
claimAtB state = farValue (reverseSwap aggregateSwap) state

portfolio-A-at : ∀ state → sum (λ j → B.holdingsA j ·ᵣ farValue (B.swaps j) state) ≡ claimAtA state
portfolio-A-at state = ℝ!

portfolio-B-at : ∀ state → sum (λ j → B.holdingsB j ·ᵣ farValue (B.swaps j) state) ≡ claimAtB state
portfolio-B-at state = ℝ!

collateralAtB : FXState → ℝ
collateralAtB state = eligibleCollateral 0 (rat [ 4 / 5 ]) (spot state) 10

-- Link the original per-trade scenario valuations to the same portfolios
-- valued at an arbitrary common-date quote above.
original-A-mark : ∀ i → B.claimA i ≡ claimAtA (B.states F.zero i)
original-A-mark F.zero = ℝ!
original-A-mark (F.suc F.zero) = ℝ!
original-A-mark (F.suc (F.suc F.zero)) = ℝ!
original-A-mark (F.suc (F.suc (F.suc F.zero))) = ℝ!

original-B-mark : ∀ i → B.claimB i ≡ claimAtB (B.states F.zero i)
original-B-mark F.zero = ℝ!
original-B-mark (F.suc F.zero) = ℝ!
original-B-mark (F.suc (F.suc F.zero)) = ℝ!
original-B-mark (F.suc (F.suc (F.suc F.zero))) = ℝ!

original-B-collateral : ∀ i → B.collateralB i ≡ collateralAtB (B.states F.zero i)
original-B-collateral i = refl

box : FXBox
box = JointMoveExample.jointBox

-- Every original single-factor scenario lies in this larger joint box.
original-scenarios-in-box : ∀ i → InBox box (B.states F.zero i)
original-scenarios-in-box F.zero = in-box
  (within decℚ≤ᵣ? decℚ≤ᵣ?) (within decℚ≤ᵣ? decℚ≤ᵣ?) (within decℚ≤ᵣ? decℚ≤ᵣ?)
original-scenarios-in-box (F.suc F.zero) = in-box
  (within decℚ≤ᵣ? decℚ≤ᵣ?) (within decℚ≤ᵣ? decℚ≤ᵣ?) (within decℚ≤ᵣ? decℚ≤ᵣ?)
original-scenarios-in-box (F.suc (F.suc F.zero)) = in-box
  (within decℚ≤ᵣ? decℚ≤ᵣ?) (within decℚ≤ᵣ? decℚ≤ᵣ?) (within decℚ≤ᵣ? decℚ≤ᵣ?)
original-scenarios-in-box (F.suc (F.suc (F.suc F.zero))) = in-box
  (within decℚ≤ᵣ? decℚ≤ᵣ?) (within decℚ≤ᵣ? decℚ≤ᵣ?) (within decℚ≤ᵣ? decℚ≤ᵣ?)

jointUp jointDown : FXState
jointUp = fx-state (rat [ 6 / 5 ]) (rat [ 9 / 10 ]) 1 decℚ<ᵣ? decℚ<ᵣ? decℚ<ᵣ?
jointDown = fx-state (rat [ 4 / 5 ]) 1 (rat [ 9 / 10 ]) decℚ<ᵣ? decℚ<ᵣ? decℚ<ᵣ?

jointUp-in-box : InBox box jointUp
jointUp-in-box = in-box
  (within decℚ≤ᵣ? decℚ≤ᵣ?) (within decℚ≤ᵣ? decℚ≤ᵣ?) (within decℚ≤ᵣ? decℚ≤ᵣ?)

jointDown-in-box : InBox box jointDown
jointDown-in-box = in-box
  (within decℚ≤ᵣ? decℚ≤ᵣ?) (within decℚ≤ᵣ? decℚ≤ᵣ?) (within decℚ≤ᵣ? decℚ≤ᵣ?)

-- All real quote states in the box are covered, not just a finite sample.
joint-A-covered : ∀ state → InBox box state → claimAtA state ≤ᵣ 5 +ᵣ 25
joint-A-covered state member = isTrans≤≡ᵣ _ _ _
  (far-value-upper aggregateSwap box state decℚ≤ᵣ? member) ℝ!

collateral-B-floor : ∀ state → InBox box state → rat [ 32 / 5 ] ≤ᵣ collateralAtB state
collateral-B-floor state member = isTrans≡≤ᵣ _ _ _ endpoint
  (eligibleCollateral-spot-monotone 0 (rat [ 4 / 5 ]) (rat [ 4 / 5 ]) (spot state) 10
    decℚ≤ᵣ? decℚ≤ᵣ? (aboveLo (spotWithin member)))
  where
  endpoint : rat [ 32 / 5 ] ≡ eligibleCollateral 0 (rat [ 4 / 5 ]) (rat [ 4 / 5 ]) 10
  endpoint = ℝ!

joint-B-covered : ∀ state → InBox box state →
  claimAtB state ≤ᵣ collateralAtB state +ᵣ rat [ 108 / 5 ]
joint-B-covered state member = isTrans≤ᵣ _ _ _
  (snd (reversed-value-bounds aggregateSwap box state decℚ≤ᵣ? member))
  (isTrans≡≤ᵣ _ _ _ endpoint
    (≤ᵣ-+o _ _ (rat [ 108 / 5 ]) (collateral-B-floor state member)))
  where
  endpoint : -ᵣ lowerValue aggregateSwap box ≡ rat [ 32 / 5 ] +ᵣ rat [ 108 / 5 ]
  endpoint = ℝ!

-- Attaining joint states prove minimality; no constructive supremum or
-- choice of a maximizing arbitrary real state is assumed.
jointBindingA : Scenario.BindingScenario (InBox box) claimAtA (λ _ → 5) 25
jointBindingA .Scenario.binding-state = jointUp
jointBindingA .Scenario.binding-admissible = jointUp-in-box
jointBindingA .Scenario.binding-equation = ℝ!

jointBindingB : Scenario.BindingScenario (InBox box) claimAtB collateralAtB (rat [ 108 / 5 ])
jointBindingB .Scenario.binding-state = jointDown
jointBindingB .Scenario.binding-admissible = jointDown-in-box
jointBindingB .Scenario.binding-equation = ℝ!

jointCertificateA : Scenario.MarginCertificate (InBox box) claimAtA (λ _ → 5) 25
jointCertificateA = Scenario.certificate-from-binding decℚ≤ᵣ? joint-A-covered jointBindingA

jointCertificateB : Scenario.MarginCertificate (InBox box) claimAtB collateralAtB (rat [ 108 / 5 ])
jointCertificateB = Scenario.certificate-from-binding decℚ≤ᵣ? joint-B-covered jointBindingB

corner-A-forces : ∀ b → claimAtA jointUp ≤ᵣ 5 +ᵣ b → 25 ≤ᵣ b
corner-A-forces = Scenario.coverage-forces-difference (claimAtA jointUp) 5 25
  (Scenario.binding-equation jointBindingA)

corner-B-forces : ∀ b → claimAtB jointDown ≤ᵣ collateralAtB jointDown +ᵣ b →
  rat [ 108 / 5 ] ≤ᵣ b
corner-B-forces = Scenario.coverage-forces-difference (claimAtB jointDown)
  (collateralAtB jointDown) (rat [ 108 / 5 ]) (Scenario.binding-equation jointBindingB)

AllQuotesA AllQuotesB : ℝ → Type₀
AllQuotesA = Scenario.Coverage (InBox box) claimAtA (λ _ → 5)
AllQuotesB = Scenario.Coverage (InBox box) claimAtB collateralAtB

joint-A-least : ∀ b → AllQuotesA b → 25 ≤ᵣ b
joint-A-least = Scenario.binding-least jointBindingA

joint-B-least : ∀ b → AllQuotesB b → rat [ 108 / 5 ] ≤ᵣ b
joint-B-least = Scenario.binding-least jointBindingB

joint-A-budget≃all-quotes : ∀ b → (25 ≤ᵣ b) ≃ AllQuotesA b
joint-A-budget≃all-quotes = Scenario.binding-budget≃coverage jointCertificateA jointBindingA

joint-B-budget≃all-quotes : ∀ b → (rat [ 108 / 5 ] ≤ᵣ b) ≃ AllQuotesB b
joint-B-budget≃all-quotes = Scenario.binding-budget≃coverage jointCertificateB jointBindingB

joint-margin-policy-path : ∀ b → (rat [ 108 / 5 ] ≤ᵣ b) ≡ AllQuotesB b
joint-margin-policy-path = Scenario.binding-policy-path jointCertificateB jointBindingB

-- The two explicit attaining states are enough to encode exact rational
-- reports. The universal proofs above additionally cover the whole box.
jointStates : Fin 2 → FXState
jointStates F.zero = jointUp
jointStates (F.suc F.zero) = jointDown

jointStates-in-box : ∀ i → InBox box (jointStates i)
jointStates-in-box F.zero = jointUp-in-box
jointStates-in-box (F.suc F.zero) = jointDown-in-box

jointClaimA jointClaimB jointCollateralA jointCollateralB : Vector 2
jointClaimA i = claimAtA (jointStates i)
jointClaimB i = claimAtB (jointStates i)
jointCollateralA i = 5
jointCollateralB i = collateralAtB (jointStates i)

joint-callA : requiredMargin jointClaimA jointCollateralA ≡ 25
joint-callA = margin-exact-at jointClaimA jointCollateralA 25 decℚ≤ᵣ?
  (λ i → Scenario.certificate-coverage jointCertificateA (jointStates i) (jointStates-in-box i))
  F.zero (Scenario.binding-equation jointBindingA)

joint-callB : requiredMargin jointClaimB jointCollateralB ≡ rat [ 108 / 5 ]
joint-callB = margin-exact-at jointClaimB jointCollateralB (rat [ 108 / 5 ]) decℚ≤ᵣ?
  (λ i → Scenario.certificate-coverage jointCertificateB (jointStates i) (jointStates-in-box i))
  (F.suc F.zero) (Scenario.binding-equation jointBindingB)

jointReportA : ExactMargin jointClaimA jointCollateralA
jointReportA .amount = 25
jointReportA .exact = joint-callA

jointReportB : ExactMargin jointClaimB jointCollateralB
jointReportB .amount = [ 108 / 5 ]
jointReportB .exact = joint-callB

old-A-payment-insufficient : payment-status (checkPayment jointReportA 15 ℚ.decℚ≤?) ≡ more-due
old-A-payment-insufficient = refl

old-B-payment-insufficient : payment-status (checkPayment jointReportB [ 68 / 5 ] ℚ.decℚ≤?) ≡ more-due
old-B-payment-insufficient = refl

-- These real equalities certify the further requested cash. Labels above
-- compute by rational comparison; rational representations need not be paths
-- by reduction to a chosen numerator/denominator representation.
extra-A : rat (outstandingRequest jointReportA 15) ≡ 10
extra-A = ℝ!

extra-B : rat (outstandingRequest jointReportB [ 68 / 5 ]) ≡ 8
extra-B = ℝ!

single-factor-A-budget-not-universal : AllQuotesA 15 → ⊥
single-factor-A-budget-not-universal coverage = isIrrefl<ᵣ 15
  (isTrans<≤ᵣ 15 25 15 decℚ<ᵣ? (joint-A-least 15 coverage))

single-factor-B-budget-not-universal : AllQuotesB (rat [ 68 / 5 ]) → ⊥
single-factor-B-budget-not-universal coverage = isIrrefl<ᵣ (rat [ 68 / 5 ])
  (isTrans<≤ᵣ _ _ _ decℚ<ᵣ? (joint-B-least (rat [ 68 / 5 ]) coverage))
