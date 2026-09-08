{-# OPTIONS --safe --cubical #-}

module Cubical.HITs.CauchyReals.Example.Financial.Margin.Workflow where

open import Cubical.HITs.CauchyReals.Example.Financial.Core.Finite
open import Cubical.HITs.CauchyReals.Example.Financial.Margin.Scenario
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.Shortfall
import Cubical.HITs.CauchyReals.Example.Financial.Margin.CounterpartyRisk as Credit
open import Cubical.HITs.CauchyReals.Foundation.Rationals using (ℚ; module ℚ)
open import Cubical.Relation.Nullary using (Dec; yes; no; ¬_; Discrete; Discrete→isSet)
open import Cubical.Data.FinData.Properties using (∀Dec)
open import Cubical.Data.Sum.Base using (inl; inr)
open import Cubical.Data.Empty using (⊥)
import Cubical.Data.Empty as Empty
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Foundations.Equiv using (_≃_; propBiimpl→Equiv)
open import Cubical.Foundations.Univalence using (ua)

data AssessmentStatus : Type₀ where
  passed more-due : AssessmentStatus

private
  more-due≢passed : ¬ (more-due ≡ passed)
  more-due≢passed equality = subst distinguish (sym equality) tt
    where
    distinguish : AssessmentStatus → Type₀
    distinguish passed = Unit
    distinguish more-due = ⊥

  isSetAssessmentStatus : isSet AssessmentStatus
  isSetAssessmentStatus = Discrete→isSet discrete
    where
    discrete : Discrete AssessmentStatus
    discrete passed passed = yes refl
    discrete passed more-due = no (λ proof → more-due≢passed (sym proof))
    discrete more-due passed = no more-due≢passed
    discrete more-due more-due = yes refl

-- Each coordinate is one supplied authorized client netting set. The
-- certificate is least among nonnegative domestic cash payments for THAT
-- coordinate, uniformly over every admissible state. The scenario domain
-- may be infinite and real-valued; only the client labels are finite.
module CertifiedClients {clients : ℕ} {State : Type₀}
  (Allowed : State → Type₀) (claims collateral : State → Vector clients)
  (calls : Fin clients → ℚ)
  (certificates : ∀ client → MarginCertificate Allowed
    (λ state → claims state client) (λ state → collateral state client) (rat (calls client))) where

  Payments : Type₀
  Payments = Fin clients → ℚ

  NonnegativePayments : Payments → Type₀
  NonnegativePayments paid = ∀ client → 0 ℚ.≤ paid client

  -- This is an actual collateral state: each payment was received in
  -- domestic cash, is eligible at par, and is available to that client
  -- netting set at closeout. Computing a request does not change this state.
  postedCollateral : Payments → State → Vector clients
  postedCollateral paid state client = collateral state client +ᵣ rat (paid client)

  ClientCovered : Payments → Fin clients → Type₀
  ClientCovered paid client = ∀ state → Allowed state →
    claims state client ≤ᵣ postedCollateral paid state client

  AllClientsCovered : Payments → Type₀
  AllClientsCovered paid = ∀ state → Allowed state →
    ∀ client → claims state client ≤ᵣ postedCollateral paid state client

  CallBounds : Payments → Type₀
  CallBounds paid = ∀ client → calls client ℚ.≤ paid client

  bounds→coverage : ∀ paid → CallBounds paid → AllClientsCovered paid
  bounds→coverage paid bounds state member client =
    certificate-bound→coverage (certificates client) (rat (paid client))
      (≤ℚ→≤ᵣ (calls client) (paid client) (bounds client)) state member

  coverage→bounds : ∀ paid → NonnegativePayments paid → AllClientsCovered paid → CallBounds paid
  coverage→bounds paid paid₊ coverage client = ≤ᵣ→≤ℚ (calls client) (paid client)
    (certificate-least (certificates client) (rat (paid client))
      (≤ℚ→≤ᵣ 0 (paid client) (paid₊ client)) (λ state member → coverage state member client))

  -- A passing certificate connects scenario coverage directly to aggregate
  -- residual exposure and every supplied default/recovery realization.
  -- Severities may depend on both the scenario and client; no independence
  -- or positive default probability is needed.
  record CoverageGuarantee (paid : Payments) : Type₀ where
    field
      all-clients-covered : AllClientsCovered paid
      aggregate-residual-zero : ∀ state → Allowed state →
        Credit.brokerResidual (claims state) (postedCollateral paid state) ≡ 0
      all-realizations-zero : (severity : State → Credit.Severity clients) →
        ∀ state → Allowed state →
        Credit.realizedCloseoutLoss (claims state) (postedCollateral paid state) (severity state) ≡ 0
  open CoverageGuarantee public

  guarantee-from-coverage : ∀ paid → AllClientsCovered paid → CoverageGuarantee paid
  guarantee-from-coverage paid coverage .all-clients-covered = coverage
  guarantee-from-coverage paid coverage .aggregate-residual-zero state member =
    sum-cong _ (λ _ → 0)
      (λ client → stopLoss-zero-below (claims state client) (postedCollateral paid state client)
        (coverage state member client)) ∙ sum-zero clients
  guarantee-from-coverage paid coverage .all-realizations-zero severity state member =
    Credit.covered-loss-zero (claims state) (postedCollateral paid state) (severity state)
      (coverage state member)

  data Assessment (paid : Payments) : Type₀ where
    accepted : CoverageGuarantee paid → Assessment paid
    deficient : (client : Fin clients) → ¬ ClientCovered paid client → Assessment paid

  assessment-status : ∀ {paid} → Assessment paid → AssessmentStatus
  assessment-status (accepted _) = passed
  assessment-status (deficient _ _) = more-due

  -- Only finite rational comparisons execute. A failure identifies a
  -- deficient client label, and refutes its universal coverage obligation;
  -- it does not claim to select a violating arbitrary real scenario.
  assess : ∀ paid → NonnegativePayments paid → Assessment paid
  assess paid paid₊ with ∀Dec (λ client → calls client ℚ.≤ paid client)
    (λ client → ℚ.≤Dec (calls client) (paid client))
  ... | inl bounds = accepted (guarantee-from-coverage paid (bounds→coverage paid bounds))
  ... | inr (client , not-bound) = deficient client λ coverage → not-bound
    (≤ᵣ→≤ℚ (calls client) (paid client)
      (certificate-least (certificates client) (rat (paid client))
        (≤ℚ→≤ᵣ 0 (paid client) (paid₊ client)) coverage))

  checkPayments : ∀ paid → NonnegativePayments paid → Dec (AllClientsCovered paid)
  checkPayments paid paid₊ with assess paid paid₊
  ... | accepted guarantee = yes (all-clients-covered guarantee)
  ... | deficient client not-covered = no λ coverage → not-covered
    (λ state member → coverage state member client)

  assess-sound : ∀ paid paid₊ → assessment-status (assess paid paid₊) ≡ passed →
    CoverageGuarantee paid
  assess-sound paid paid₊ proof with assess paid paid₊
  ... | accepted guarantee = guarantee
  ... | deficient client not-covered = Empty.rec (more-due≢passed proof)

  assess-complete : ∀ paid paid₊ → AllClientsCovered paid →
    assessment-status (assess paid paid₊) ≡ passed
  assess-complete paid paid₊ coverage with assess paid paid₊
  ... | accepted guarantee = refl
  ... | deficient client not-covered = Empty.rec
    (not-covered (λ state member → coverage state member client))

  -- The executable pass condition and universal coverage are propositions.
  -- Their path can transport dependent operational evidence between APIs.
  pass≃coverage : ∀ paid paid₊ →
    (assessment-status (assess paid paid₊) ≡ passed) ≃ AllClientsCovered paid
  pass≃coverage paid paid₊ = propBiimpl→Equiv
    (isSetAssessmentStatus _ _) (isPropΠ3 (λ _ _ _ → isProp≤ᵣ _ _))
    (λ proof → all-clients-covered (assess-sound paid paid₊ proof))
    (assess-complete paid paid₊)

  pass-policy-path : ∀ paid paid₊ →
    (assessment-status (assess paid paid₊) ≡ passed) ≡ AllClientsCovered paid
  pass-policy-path paid paid₊ = ua (pass≃coverage paid paid₊)

  -- Requests retain the client labels even when the broker can add their
  -- domestic amounts for reporting. Overpayment produces a zero request.
  outstanding : Payments → Payments
  outstanding paid client = ℚ.max (calls client ℚ.- paid client) 0

  outstanding-nonnegative : ∀ paid → NonnegativePayments (outstanding paid)
  outstanding-nonnegative paid client = ℚ.≤max' (calls client ℚ.- paid client) 0

  private
    outstanding-as-shortfall : ∀ paid client →
      rat (outstanding paid client) ≡ stopLoss (rat (calls client)) (rat (paid client))
    outstanding-as-shortfall paid client = sym (stopLoss-rat (calls client) (paid client))

    call-covered-by-request : ∀ paid client →
      rat (calls client) ≤ᵣ rat (paid client) +ᵣ rat (outstanding paid client)
    call-covered-by-request paid client = isTrans≤≡ᵣ _ _ _
      (stopLoss-reconstruct (rat (calls client)) (rat (paid client)))
      (cong (rat (paid client) +ᵣ_) (sym (outstanding-as-shortfall paid client)))

  -- Competitors may offer arbitrary nonnegative Cauchy-real further cash,
  -- so the minimality theorem is stronger than a rational-grid comparison.
  FurtherCoverage : Payments → Vector clients → Type₀
  FurtherCoverage paid further = ∀ state → Allowed state → ∀ client →
    claims state client ≤ᵣ postedCollateral paid state client +ᵣ further client

  requests-cover : ∀ paid → FurtherCoverage paid (λ client → rat (outstanding paid client))
  requests-cover paid state member client = isTrans≤≡ᵣ _ _ _
    (certificate-bound→coverage (certificates client)
      (rat (paid client) +ᵣ rat (outstanding paid client))
      (call-covered-by-request paid client) state member)
    (+ᵣAssoc (collateral state client) (rat (paid client)) (rat (outstanding paid client)))

  requests-componentwise-minimal : ∀ paid → NonnegativePayments paid →
    (further : Vector clients) → (∀ client → 0 ≤ᵣ further client) →
    FurtherCoverage paid further → ∀ client → rat (outstanding paid client) ≤ᵣ further client
  requests-componentwise-minimal paid paid₊ further further₊ coverage client =
    isTrans≡≤ᵣ _ _ _ (outstanding-as-shortfall paid client)
      (stopLoss-upper (rat (calls client)) (rat (paid client)) (further client) (further₊ client)
        (certificate-least (certificates client) (rat (paid client) +ᵣ further client)
          (nonnegative-add (rat (paid client)) (further client)
            (≤ℚ→≤ᵣ 0 (paid client) (paid₊ client)) (further₊ client))
          (λ state member → isTrans≤≡ᵣ _ _ _ (coverage state member client)
            (sym (+ᵣAssoc (collateral state client) (rat (paid client)) (further client))))))

  totalOutstanding : Payments → ℝ
  totalOutstanding paid = sum (λ client → rat (outstanding paid client))

  requests-total-minimal : ∀ paid → NonnegativePayments paid →
    (further : Vector clients) → (∀ client → 0 ≤ᵣ further client) →
    FurtherCoverage paid further → totalOutstanding paid ≤ᵣ sum further
  requests-total-minimal paid paid₊ further further₊ coverage =
    sum-monotone (λ client → rat (outstanding paid client)) further
      (requests-componentwise-minimal paid paid₊ further further₊ coverage)

  -- afterRequests describes receipt of the computed requests; a request
  -- alone is not a payment. Addition remains componentwise by client.
  afterRequests : Payments → Payments
  afterRequests paid client = paid client ℚ.+ outstanding paid client

  afterRequests-nonnegative : ∀ paid → NonnegativePayments paid →
    NonnegativePayments (afterRequests paid)
  afterRequests-nonnegative paid paid₊ client = ≤ᵣ→≤ℚ 0 (afterRequests paid client)
    (isTrans≤≡ᵣ _ _ _
      (nonnegative-add (rat (paid client)) (rat (outstanding paid client))
        (≤ℚ→≤ᵣ 0 (paid client) (paid₊ client))
        (≤ℚ→≤ᵣ 0 (outstanding paid client) (outstanding-nonnegative paid client)))
      (+ᵣ-rat (paid client) (outstanding paid client)))

  afterRequests-coverage : ∀ paid → AllClientsCovered (afterRequests paid)
  afterRequests-coverage paid state member client = isTrans≤≡ᵣ _ _ _
    (requests-cover paid state member client)
    (sym (+ᵣAssoc (collateral state client) (rat (paid client)) (rat (outstanding paid client)))
      ∙ cong (collateral state client +ᵣ_) (+ᵣ-rat (paid client) (outstanding paid client)))

  requests-guarantee : ∀ paid → CoverageGuarantee (afterRequests paid)
  requests-guarantee paid = guarantee-from-coverage (afterRequests paid) (afterRequests-coverage paid)

  requests-pass : ∀ paid paid₊ →
    assessment-status (assess (afterRequests paid) (afterRequests-nonnegative paid paid₊)) ≡ passed
  requests-pass paid paid₊ = assess-complete (afterRequests paid)
    (afterRequests-nonnegative paid paid₊) (afterRequests-coverage paid)
