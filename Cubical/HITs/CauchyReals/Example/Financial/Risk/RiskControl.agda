module Cubical.HITs.CauchyReals.Example.Financial.Risk.RiskControl where

open import Cubical.HITs.CauchyReals.Example.Financial.Risk.ExpectedShortfall
open import Cubical.HITs.CauchyReals.Foundation.Rationals using (ℚ; module ℚ)
open import Cubical.HITs.CauchyReals.Algebra.Order.Properties using (isIrrefl<ᵣ)
open import Cubical.Relation.Nullary using (yes; no; ¬_)
import Cubical.HITs.PropositionalTruncation as PT

-- This is a total, constructive budget checker for certified numerical
-- bounds. Only RATIONAL comparisons branch; arbitrary real order is untouched.
data Decision : Type₀ where
  pass fail unknown : Decision

module Control {n : ℕ} (P : Distribution n) (level : TailLevel) where
  open TailRisk P level

  record Report (X : Vector n) : Type₀ where
    field
      trialThreshold : ℝ
      stressDistribution : Distribution n
      densityBound : Admissible stressDistribution
      lower upper : ℚ
      lower-valid : rat lower ≤ᵣ expectation stressDistribution X
      upper-valid : objective X trialThreshold ≤ᵣ rat upper
  open Report public

  report-consistent : ∀ X (report : Report X) → rat (lower report) ≤ᵣ rat (upper report)
  report-consistent X report = isTrans≤ᵣ _ _ _ (lower-valid report)
    (isTrans≤ᵣ _ _ _
      (weak-duality X (stressDistribution report) (densityBound report) (trialThreshold report))
      (upper-valid report))

  approve : ∀ X (report : Report X) budget → upper report ℚ.≤ budget →
    Accepted X (rat budget)
  approve X report budget p = PT.∣ trialThreshold report ,
    isTrans≤ᵣ _ _ _ (upper-valid report) (≤ℚ→≤ᵣ _ _ p) ∣₁

  reject : ∀ X (report : Report X) budget → budget ℚ.< lower report →
    ¬ Accepted X (rat budget)
  reject X report budget p accepted = isIrrefl<ᵣ (rat budget)
    (isTrans<≤ᵣ _ _ _ (<ℚ→<ᵣ _ _ p)
      (isTrans≤ᵣ _ _ _ (lower-valid report)
        (accepted-sound X (rat budget) accepted
          (stressDistribution report) (densityBound report))))

  data Verdict (X : Vector n) (budget : ℚ) : Type₀ where
    approved : Accepted X (rat budget) → Verdict X budget
    rejected : ¬ Accepted X (rat budget) → Verdict X budget
    inconclusive : Verdict X budget

  decision : ∀ {X budget} → Verdict X budget → Decision
  decision (approved _) = pass
  decision (rejected _) = fail
  decision inconclusive = unknown

  check : ∀ X → Report X → (budget : ℚ) → Verdict X budget
  check X report budget with ℚ.≤Dec (upper report) budget
  ... | yes upper≤budget = approved (approve X report budget upper≤budget)
  ... | no _ with ℚ.<Dec budget (lower report)
  ...   | yes budget<lower = rejected (reject X report budget budget<lower)
  ...   | no _ = inconclusive

  -- A rejected report proves that no threshold could certify this budget;
  -- an inconclusive report may need tighter numerical bounds or better
  -- primal/dual trial witnesses. It makes no claim about budget compliance.
  DecisionEvidence : ∀ X budget → Decision → Type₀
  DecisionEvidence X budget pass = Accepted X (rat budget)
  DecisionEvidence X budget fail = ¬ Accepted X (rat budget)
  DecisionEvidence X budget unknown = Unit

  verdict-sound : ∀ X budget (v : Verdict X budget) →
    DecisionEvidence X budget (decision v)
  verdict-sound X budget (approved proof) = proof
  verdict-sound X budget (rejected proof) = proof
  verdict-sound X budget inconclusive = tt

  check-sound : ∀ X report budget →
    DecisionEvidence X budget (decision (check X report budget))
  check-sound X report budget = verdict-sound X budget (check X report budget)
