{-# OPTIONS --safe --cubical #-}

-- Stage 2: universal scenario coverage and certified rational enclosures.
-- REFERENCES.md#robust-optimization and #bcbs-fx-2013 motivate the obligations;
-- the constructive enclosure/checker interface is proved here.
module Cubical.HITs.CauchyReals.Example.Financial.Broker.Stage02Scenarios where

open import Cubical.HITs.CauchyReals.Example.Financial.Broker.Stage01Cash
open import Cubical.HITs.CauchyReals.Foundation.Rationals using (ℚ; module ℚ)
open import Cubical.Relation.Nullary using (Dec; yes; no; ¬_)
import Cubical.Data.Empty as Empty
import Cubical.HITs.CauchyReals.Example.Financial.Margin.Scenario as Margin
import Cubical.HITs.CauchyReals.Example.Financial.Margin.Base as Finite
open import Cubical.Data.Unit using (Unit)

module ScenarioAccount {State : Type₀} (Allowed : State → Type₀)
  (claims collateral : State → ℝ) where

  Coverage : ℝ → Type₀
  Coverage = Margin.Coverage Allowed claims collateral

  -- Sufficient cash bounds are useful even when the least real requirement
  -- is not known exactly. No procedure deciding arbitrary real order is used.
  record UpperRequirement : Type₀ where
    field
      amount : ℝ
      nonnegative : 0 ≤ᵣ amount
      covers : Coverage amount
  open UpperRequirement public

  upper-from-minimum : ∀ m → Margin.MarginCertificate Allowed claims collateral m → UpperRequirement
  upper-from-minimum m certificate .amount = m
  upper-from-minimum m certificate .nonnegative = Margin.certificate-nonnegative certificate
  upper-from-minimum m certificate .covers = Margin.certificate-coverage certificate

  record Report : Type₀ where
    field
      lower upper : ℚ
      lower-nonnegative : 0 ℚ.≤ lower
      upper-nonnegative : 0 ℚ.≤ upper
      upper-covers : Coverage (rat upper)
      lower-required : ∀ b → 0 ≤ᵣ b → Coverage b → rat lower ≤ᵣ b
  open Report public

  report-ordered : ∀ report → lower report ℚ.≤ upper report
  report-ordered report = ≤ᵣ→≤ℚ _ _
    (lower-required report (rat (upper report))
      (≤ℚ→≤ᵣ _ _ (upper-nonnegative report)) (upper-covers report))

  -- A conservative upper certificate alone always gives a valid enclosure.
  conservative-report : ∀ q → 0 ℚ.≤ q → Coverage (rat q) → Report
  conservative-report q q₊ coverage .lower = 0
  conservative-report q q₊ coverage .upper = q
  conservative-report q q₊ coverage .lower-nonnegative = ℚ.isRefl≤ 0
  conservative-report q q₊ coverage .upper-nonnegative = q₊
  conservative-report q q₊ coverage .upper-covers = coverage
  conservative-report q q₊ coverage .lower-required b b₊ covered = b₊

  exact-report : ∀ q → Margin.MarginCertificate Allowed claims collateral (rat q) → Report
  exact-report q certificate .lower = q
  exact-report q certificate .upper = q
  exact-report q certificate .lower-nonnegative = ≤ᵣ→≤ℚ 0 q
    (Margin.certificate-nonnegative certificate)
  exact-report q certificate .upper-nonnegative = ≤ᵣ→≤ℚ 0 q
    (Margin.certificate-nonnegative certificate)
  exact-report q certificate .upper-covers = Margin.certificate-coverage certificate
  exact-report q certificate .lower-required = Margin.certificate-least certificate

  upper-bound→coverage : ∀ report paid → upper report ℚ.≤ paid → Coverage (rat paid)
  upper-bound→coverage report paid bound state member = isTrans≤ᵣ _ _ _
    (upper-covers report state member)
    (≤ᵣ-o+ _ _ (collateral state) (≤ℚ→≤ᵣ _ _ bound))

  coverage→lower-bound : ∀ report paid → 0 ℚ.≤ paid → Coverage (rat paid) → lower report ℚ.≤ paid
  coverage→lower-bound report paid paid₊ coverage = ≤ᵣ→≤ℚ _ _
    (lower-required report (rat paid) (≤ℚ→≤ᵣ _ _ paid₊) coverage)

  data Verdict (report : Report) (paid : ℚ) : Type₀ where
    certified : Coverage (rat paid) → Verdict report paid
    deficient : ¬ Coverage (rat paid) → Verdict report paid
    undetermined : lower report ℚ.≤ paid → ¬ (upper report ℚ.≤ paid) → Verdict report paid

  assess : ∀ report paid → 0 ℚ.≤ paid → Verdict report paid
  assess report paid paid₊ with ℚ.≤Dec (upper report) paid
  ... | yes enough = certified (upper-bound→coverage report paid enough)
  ... | no not-upper with ℚ.≤Dec (lower report) paid
  ...   | yes lower≤paid = undetermined lower≤paid not-upper
  ...   | no not-lower = deficient (λ coverage → not-lower (coverage→lower-bound report paid paid₊ coverage))

  -- Completeness becomes available precisely when the enclosure is exact.
  -- An inconclusive coarse report never asserts that the account is unsafe.
  assess-exact : ∀ report → lower report ≡ upper report →
    ∀ paid → 0 ℚ.≤ paid → Dec (Coverage (rat paid))
  assess-exact report tight paid paid₊ with assess report paid paid₊
  ... | certified coverage = yes coverage
  ... | deficient not-covered = no not-covered
  ... | undetermined lower≤paid not-upper =
    Empty.rec (not-upper (subst (ℚ._≤ paid) tight lower≤paid))

  -- Stage 1 is the local account at an admissible scenario. The universal
  -- certificate supplies its post-receipt safety obligation at every state.
  covered-account : ∀ state → Allowed state → (collateral₊ : 0 ≤ᵣ collateral state) →
    ∀ paid paid₊ → Coverage paid → Covered (receive (account (claims state) (collateral state) collateral₊) paid paid₊)
  covered-account state member collateral₊ paid paid₊ coverage = coverage state member

-- Finite lattice folds construct an exact REAL minimum; converting it to
-- an exact rational report still requires a supplied equality to a rational.
finite-upper : ∀ {n} (X C : Vector (suc n)) →
  ScenarioAccount.UpperRequirement (λ _ → Unit) X C
finite-upper X C = ScenarioAccount.upper-from-minimum (λ _ → Unit) X C
  (Finite.requiredMargin X C) (Finite.finite-margin-certificate X C)
