{-# OPTIONS --safe --cubical #-}

module Cubical.HITs.CauchyReals.Example.Financial.Margin.CounterpartyRisk where

open import Cubical.HITs.CauchyReals.Example.Financial.Margin.ClientNetting public
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.Shortfall
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.ExpectedShortfall
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.WorstCase
open import Cubical.Foundations.Equiv using (_≃_; propBiimpl→Equiv)
open import Cubical.Data.Bool.Base using (Bool; false; true)
open import Cubical.Tactics.CommRingSolver.Specialised.Reals

-- Supplied realized severities combine occurrence of default and the
-- unrecovered fraction of an unsecured claim, separately for each netting
-- set. They are not probabilities of default, and no PD model is inferred.
record Severity (clients : ℕ) : Type₀ where
  constructor severity
  field
    coefficients : Vector clients
    coefficient-nonnegative : ∀ i → 0 ≤ᵣ coefficients i
    coefficient-at-most-one : ∀ i → coefficients i ≤ᵣ 1
open Severity public

zeroSeverity totalLossSeverity : ∀ {clients} → Severity clients
zeroSeverity = severity (λ _ → 0) (λ _ → ≤ᵣ-refl 0) (λ _ → decℚ≤ᵣ?)
totalLossSeverity = severity (λ _ → 1) (λ _ → decℚ≤ᵣ?) (λ _ → ≤ᵣ-refl 1)

private
  on-default : Bool → ℝ → ℝ
  on-default false x = 0
  on-default true x = x

  on-default-nonnegative : ∀ b x → 0 ≤ᵣ x → 0 ≤ᵣ on-default b x
  on-default-nonnegative false x p = ≤ᵣ-refl 0
  on-default-nonnegative true x p = p

  on-default-at-most-one : ∀ b x → x ≤ᵣ 1 → on-default b x ≤ᵣ 1
  on-default-at-most-one false x p = decℚ≤ᵣ?
  on-default-at-most-one true x p = p

-- A Boolean default indicator times a supplied unrecovered fraction is
-- an admissible severity. The indicator may vary with the scenario.
defaultSeverity : ∀ {clients} → (Fin clients → Bool) → Severity clients → Severity clients
defaultSeverity occurred unrecovered = severity
  (λ i → on-default (occurred i) (coefficients unrecovered i))
  (λ i → on-default-nonnegative (occurred i) (coefficients unrecovered i)
    (coefficient-nonnegative unrecovered i))
  (λ i → on-default-at-most-one (occurred i) (coefficients unrecovered i)
    (coefficient-at-most-one unrecovered i))

-- Claims and effective collateral use the same currency units and horizon.
-- Collateral credited here is assumed available for this closeout and
-- enforceable for this specific netting set; a mere posting promise is not
-- proof of those conditions. Settlement principal and funding remain separate.
realizedCloseoutLoss : ∀ {clients} → Vector clients → Vector clients → Severity clients → ℝ
realizedCloseoutLoss claims collateral θ =
  sum (λ i → coefficients θ i ·ᵣ stopLoss (claims i) (collateral i))

loss-nonnegative : ∀ {clients} (claims collateral : Vector clients) θ →
  0 ≤ᵣ realizedCloseoutLoss claims collateral θ
loss-nonnegative claims collateral θ = sum-nonnegative _
  (λ i → nonnegative-mul (coefficients θ i) _ (coefficient-nonnegative θ i)
    (stopLoss-nonnegative (claims i) (collateral i)))

loss≤brokerResidual : ∀ {clients} (claims collateral : Vector clients) θ →
  realizedCloseoutLoss claims collateral θ ≤ᵣ brokerResidual claims collateral
loss≤brokerResidual claims collateral θ = sum-monotone _ _ λ i →
  isTrans≤≡ᵣ _ _ _
    (≤ᵣ-·ᵣo (coefficients θ i) 1 (stopLoss (claims i) (collateral i))
      (stopLoss-nonnegative (claims i) (collateral i)) (coefficient-at-most-one θ i))
    (·IdLᵣ (stopLoss (claims i) (collateral i)))

severity-monotone : ∀ {clients} (claims collateral : Vector clients) θ η →
  (∀ i → coefficients θ i ≤ᵣ coefficients η i) →
  realizedCloseoutLoss claims collateral θ ≤ᵣ realizedCloseoutLoss claims collateral η
severity-monotone claims collateral θ η bound = sum-monotone _ _ λ i →
  ≤ᵣ-·ᵣo (coefficients θ i) (coefficients η i) (stopLoss (claims i) (collateral i))
    (stopLoss-nonnegative (claims i) (collateral i)) (bound i)

loss-claims-monotone : ∀ {clients} (X Y collateral : Vector clients) θ →
  (∀ i → X i ≤ᵣ Y i) →
  realizedCloseoutLoss X collateral θ ≤ᵣ realizedCloseoutLoss Y collateral θ
loss-claims-monotone X Y collateral θ bound = sum-monotone _ _ λ i →
  ≤ᵣ-o·ᵣ _ _ (coefficients θ i) (coefficient-nonnegative θ i)
    (stopLoss-monotone (X i) (Y i) (collateral i) (bound i))

loss-collateral-antitone : ∀ {clients} (claims C D : Vector clients) θ →
  (∀ i → C i ≤ᵣ D i) →
  realizedCloseoutLoss claims D θ ≤ᵣ realizedCloseoutLoss claims C θ
loss-collateral-antitone claims C D θ bound = sum-monotone _ _ λ i →
  ≤ᵣ-o·ᵣ _ _ (coefficients θ i) (coefficient-nonnegative θ i)
    (stopLoss-antitone-threshold (claims i) (C i) (D i) (bound i))

covered-loss-zero : ∀ {clients} (claims collateral : Vector clients) θ →
  (∀ i → claims i ≤ᵣ collateral i) → realizedCloseoutLoss claims collateral θ ≡ 0
covered-loss-zero {clients} claims collateral θ covered = sum-cong _ (λ _ → 0)
  (λ i → cong (coefficients θ i ·ᵣ_) (stopLoss-zero-below (claims i) (collateral i) (covered i))
    ∙ Rℝ.0RightAnnihilates (coefficients θ i))
  ∙ sum-zero clients

zero-severity-loss : ∀ {clients} (claims collateral : Vector clients) →
  realizedCloseoutLoss claims collateral zeroSeverity ≡ 0
zero-severity-loss {clients} claims collateral = sum-cong _ (λ _ → 0)
  (λ i → Rℝ.0LeftAnnihilates (stopLoss (claims i) (collateral i))) ∙ sum-zero clients

total-severity-loss : ∀ {clients} (claims collateral : Vector clients) →
  realizedCloseoutLoss claims collateral totalLossSeverity ≡ brokerResidual claims collateral
total-severity-loss claims collateral = sum-cong _ _
  (λ i → ·IdLᵣ (stopLoss (claims i) (collateral i)))

-- Exposure is an exact robust bound over ALL admissible severities, since
-- the all-default, zero-recovery severity attains it. This is a scenario
-- envelope, not an assertion that this severity is probable or forecast.
residual-budget-covers-all-severities : ∀ {clients} (claims collateral : Vector clients) budget →
  brokerResidual claims collateral ≤ᵣ budget →
  (θ : Severity clients) → realizedCloseoutLoss claims collateral θ ≤ᵣ budget
residual-budget-covers-all-severities claims collateral budget bound θ =
  isTrans≤ᵣ _ _ _ (loss≤brokerResidual claims collateral θ) bound

all-severities-bound→residual : ∀ {clients} (claims collateral : Vector clients) budget →
  ((θ : Severity clients) → realizedCloseoutLoss claims collateral θ ≤ᵣ budget) →
  brokerResidual claims collateral ≤ᵣ budget
all-severities-bound→residual claims collateral budget bound = isTrans≡≤ᵣ _ _ _
  (sym (total-severity-loss claims collateral)) (bound totalLossSeverity)

residual-budget≃all-severities : ∀ {clients} (claims collateral : Vector clients) budget →
  (brokerResidual claims collateral ≤ᵣ budget) ≃
  ((θ : Severity clients) → realizedCloseoutLoss claims collateral θ ≤ᵣ budget)
residual-budget≃all-severities claims collateral budget = propBiimpl→Equiv
  (isProp≤ᵣ _ _) (isPropΠ (λ _ → isProp≤ᵣ _ _))
  (residual-budget-covers-all-severities claims collateral budget)
  (all-severities-bound→residual claims collateral budget)

-- The scenario index is outside the client index. Thus severity may depend
-- on both market conditions and client identity; independence is not assumed.
ClaimScenarios : ℕ → ℕ → Type₀
ClaimScenarios clients scenarios = Fin scenarios → Vector clients

scenarioExposure : ∀ {clients scenarios} →
  ClaimScenarios clients scenarios → ClaimScenarios clients scenarios → Vector scenarios
scenarioExposure claims collateral ω = brokerResidual (claims ω) (collateral ω)

scenarioLoss : ∀ {clients scenarios} →
  ClaimScenarios clients scenarios → ClaimScenarios clients scenarios →
  (Fin scenarios → Severity clients) → Vector scenarios
scenarioLoss claims collateral θ ω = realizedCloseoutLoss (claims ω) (collateral ω) (θ ω)

scenario-loss≤exposure : ∀ {clients scenarios}
  (claims collateral : ClaimScenarios clients scenarios) θ ω →
  scenarioLoss claims collateral θ ω ≤ᵣ scenarioExposure claims collateral ω
scenario-loss≤exposure claims collateral θ ω = loss≤brokerResidual (claims ω) (collateral ω) (θ ω)

worstCase-loss≤exposure : ∀ {clients scenarios}
  (claims collateral : ClaimScenarios clients (suc scenarios)) θ →
  worstCase (scenarioLoss claims collateral θ) ≤ᵣ worstCase (scenarioExposure claims collateral)
worstCase-loss≤exposure claims collateral θ = worstCase-monotone
  (scenarioLoss claims collateral θ) (scenarioExposure claims collateral)
  (scenario-loss≤exposure claims collateral θ)

expectation-loss≤exposure : ∀ {clients scenarios} (P : Distribution scenarios)
  (claims collateral : ClaimScenarios clients scenarios) θ →
  expectation P (scenarioLoss claims collateral θ) ≤ᵣ expectation P (scenarioExposure claims collateral)
expectation-loss≤exposure P claims collateral θ = expectation-monotone P
  (scenarioLoss claims collateral θ) (scenarioExposure claims collateral)
  (scenario-loss≤exposure claims collateral θ)

module ScenarioRisk {clients scenarios : ℕ} (P : Distribution scenarios) (level : TailLevel)
  (claims collateral : ClaimScenarios clients scenarios) where
  module Tail = TailRisk P level

  -- Any certificate for the exposure profile is safe for every supplied
  -- realization of severities. No optimizer or default sample is selected.
  exposure-budget→loss-budget : ∀ budget → Tail.Accepted (scenarioExposure claims collateral) budget →
    (θ : Fin scenarios → Severity clients) → Tail.Accepted (scenarioLoss claims collateral θ) budget
  exposure-budget→loss-budget budget accepted θ = Tail.accepted-monotone
    (scenarioLoss claims collateral θ) (scenarioExposure claims collateral) budget
    (scenario-loss≤exposure claims collateral θ) accepted

  all-loss-budgets→exposure-budget : ∀ budget →
    ((θ : Fin scenarios → Severity clients) → Tail.Accepted (scenarioLoss claims collateral θ) budget) →
    Tail.Accepted (scenarioExposure claims collateral) budget
  all-loss-budgets→exposure-budget budget accepted = subst (λ X → Tail.Accepted X budget)
    (funExt (λ ω → total-severity-loss (claims ω) (collateral ω)))
    (accepted (λ _ → totalLossSeverity))

  exposure-budget≃all-loss-budgets : ∀ budget →
    Tail.Accepted (scenarioExposure claims collateral) budget ≃
    ((θ : Fin scenarios → Severity clients) → Tail.Accepted (scenarioLoss claims collateral θ) budget)
  exposure-budget≃all-loss-budgets budget = propBiimpl→Equiv
    (Tail.accepted-isProp _ budget) (isPropΠ (λ _ → Tail.accepted-isProp _ budget))
    (exposure-budget→loss-budget budget) (all-loss-budgets→exposure-budget budget)
