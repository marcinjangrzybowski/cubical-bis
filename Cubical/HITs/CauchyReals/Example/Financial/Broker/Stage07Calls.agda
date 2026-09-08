{-# OPTIONS --safe --cubical #-}

-- Generic minimum-transfer call policy. Literature motivation:
-- REFERENCES.md#bcbs-iosco-2020 and #brigo-pallavicini-2014.
-- The threshold and its equality convention are explicit policy inputs.
-- This is a mathematical tolerance policy, not a regulatory calibration.
module Cubical.HITs.CauchyReals.Example.Financial.Broker.Stage07Calls where

open import Cubical.HITs.CauchyReals.Example.Financial.Core.Finite
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.Shortfall
open import Cubical.HITs.CauchyReals.Example.Financial.Margin.Scenario using
  (MarginCertificate; certificate-coverage; certificate-nonnegative)
import Cubical.HITs.CauchyReals.Example.Financial.Margin.CounterpartyRisk as Credit
open import Cubical.HITs.CauchyReals.Foundation.Rationals using (ℚ; module ℚ)
open import Cubical.Relation.Nullary using (yes; no)
open import Cubical.Tactics.CommRingSolver.Specialised.Reals

-- A gap exactly equal to the minimum transfer amount is left outstanding.
-- Above that threshold the entire gap is requested, not just its excess.
transferAmount : ℚ → ℚ → ℚ
transferAmount gap mta with ℚ.≤Dec gap mta
... | yes _ = 0
... | no _ = gap

transferAmount-nonnegative : ∀ gap mta → 0 ℚ.≤ gap → 0 ℚ.≤ transferAmount gap mta
transferAmount-nonnegative gap mta gap₊ with ℚ.≤Dec gap mta
... | yes _ = ℚ.decℚ≤?
... | no _ = gap₊

-- The unrequested portion is bounded by the supplied nonnegative tolerance.
transferAmount-tolerance : ∀ gap mta → 0 ℚ.≤ mta →
  rat gap ≤ᵣ rat (transferAmount gap mta) +ᵣ rat mta
transferAmount-tolerance gap mta mta₊ with ℚ.≤Dec gap mta
... | yes gap≤mta = isTrans≤≡ᵣ _ _ _ (≤ℚ→≤ᵣ gap mta gap≤mta) (sym (+IdL (rat mta)))
... | no _ = isTrans≡≤ᵣ _ _ _ (sym (+IdR (rat gap)))
  (≤ᵣ-o+ 0 (rat mta) (rat gap) (≤ℚ→≤ᵣ 0 mta mta₊))

-- Rational upper requirements are supplied with universal coverage, not
-- assumed equal to an arbitrary Cauchy-real least margin. Conservative
-- revaluation reserves therefore instantiate this stage directly.
module MinimumTransfer {clients : ℕ} {State : Type₀}
  (Allowed : State → Type₀) (claims collateral : State → Vector clients)
  (requirements : Fin clients → ℚ)
  (requirements₊ : ∀ client → 0 ℚ.≤ requirements client)
  (requirement-covers : ∀ state → Allowed state → ∀ client →
    claims state client ≤ᵣ collateral state client +ᵣ rat (requirements client)) where

  Payments : Type₀
  Payments = Fin clients → ℚ

  NonnegativePayments : Payments → Type₀
  NonnegativePayments cash = ∀ client → 0 ℚ.≤ cash client

  rawGap : Payments → Payments
  rawGap paid client = ℚ.max (requirements client ℚ.- paid client) 0

  rawGap-nonnegative : ∀ paid → NonnegativePayments (rawGap paid)
  rawGap-nonnegative paid client = ℚ.≤max' (requirements client ℚ.- paid client) 0

  requested : Payments → Payments → Payments
  requested mta paid client = transferAmount (rawGap paid client) (mta client)

  requested-nonnegative : ∀ mta paid → NonnegativePayments (requested mta paid)
  requested-nonnegative mta paid client =
    transferAmount-nonnegative (rawGap paid client) (mta client) (rawGap-nonnegative paid client)

  -- These are balances AFTER the requested cash has actually been received,
  -- remains available for its own client netting set, and is eligible at par.
  -- Calling requested alone changes neither paid nor collateral.
  received : Payments → Payments → Payments
  received mta paid client = paid client ℚ.+ requested mta paid client

  receivedCollateral : Payments → Payments → State → Vector clients
  receivedCollateral mta paid state client = collateral state client +ᵣ rat (received mta paid client)

  received-nonnegative : ∀ mta paid → NonnegativePayments paid → NonnegativePayments (received mta paid)
  received-nonnegative mta paid paid₊ client = ≤ᵣ→≤ℚ 0 (received mta paid client)
    (isTrans≤≡ᵣ _ _ _
      (nonnegative-add (rat (paid client)) (rat (requested mta paid client))
        (≤ℚ→≤ᵣ 0 (paid client) (paid₊ client))
        (≤ℚ→≤ᵣ 0 (requested mta paid client) (requested-nonnegative mta paid client)))
      (+ᵣ-rat (paid client) (requested mta paid client)))

  private
    rawGap-covers : ∀ paid client →
      rat (requirements client) ≤ᵣ rat (paid client) +ᵣ rat (rawGap paid client)
    rawGap-covers paid client = isTrans≤≡ᵣ _ _ _
      (stopLoss-reconstruct (rat (requirements client)) (rat (paid client)))
      (cong (rat (paid client) +ᵣ_) (stopLoss-rat (requirements client) (paid client)))

  requirement-with-tolerance : ∀ mta → NonnegativePayments mta → ∀ paid client →
    rat (requirements client) ≤ᵣ rat (received mta paid client) +ᵣ rat (mta client)
  requirement-with-tolerance mta mta₊ paid client = isTrans≤ᵣ _ _ _ (rawGap-covers paid client)
    (isTrans≤≡ᵣ _ _ _
      (≤ᵣ-o+ _ _ (rat (paid client))
        (transferAmount-tolerance (rawGap paid client) (mta client) (mta₊ client)))
      (+ᵣAssoc (rat (paid client)) (rat (requested mta paid client)) (rat (mta client))
        ∙ cong (_+ᵣ rat (mta client)) (+ᵣ-rat (paid client) (requested mta paid client))))

  coverage-with-tolerance : ∀ mta → NonnegativePayments mta → ∀ paid state → Allowed state →
    ∀ client → claims state client ≤ᵣ receivedCollateral mta paid state client +ᵣ rat (mta client)
  coverage-with-tolerance mta mta₊ paid state member client = isTrans≤ᵣ _ _ _
    (requirement-covers state member client)
    (isTrans≤≡ᵣ _ _ _
      (≤ᵣ-o+ _ _ (collateral state client) (requirement-with-tolerance mta mta₊ paid client))
      (+ᵣAssoc (collateral state client) (rat (received mta paid client)) (rat (mta client))))

  client-residual-bound : ∀ mta → NonnegativePayments mta → ∀ paid state → Allowed state →
    ∀ client → stopLoss (claims state client) (receivedCollateral mta paid state client) ≤ᵣ rat (mta client)
  client-residual-bound mta mta₊ paid state member client = stopLoss-upper _ _ _
    (≤ℚ→≤ᵣ 0 (mta client) (mta₊ client)) (coverage-with-tolerance mta mta₊ paid state member client)

  totalTolerance : Payments → ℝ
  totalTolerance mta = sum (λ client → rat (mta client))

  broker-residual-bound : ∀ mta → NonnegativePayments mta → ∀ paid state → Allowed state →
    Credit.brokerResidual (claims state) (receivedCollateral mta paid state) ≤ᵣ totalTolerance mta
  broker-residual-bound mta mta₊ paid state member =
    Credit.residual-budget (claims state) (receivedCollateral mta paid state) (λ client → rat (mta client))
      (client-residual-bound mta mta₊ paid state member)

  all-losses-bound : ∀ mta → NonnegativePayments mta → ∀ paid →
    (severity : State → Credit.Severity clients) → ∀ state → Allowed state →
    Credit.realizedCloseoutLoss (claims state) (receivedCollateral mta paid state) (severity state)
      ≤ᵣ totalTolerance mta
  all-losses-bound mta mta₊ paid severity state member = isTrans≤ᵣ _ _ _
    (Credit.loss≤brokerResidual (claims state) (receivedCollateral mta paid state) (severity state))
    (broker-residual-bound mta mta₊ paid state member)

  -- One end-to-end result exposes both actual-balance validity and the
  -- tolerated exposure/loss bounds. A positive MTA does not imply zero loss.
  record CallGuarantee (mta paid : Payments) : Type₀ where
    field
      requests-valid : NonnegativePayments (requested mta paid)
      received-balances-valid : NonnegativePayments (received mta paid)
      clients-within-tolerance : ∀ state → Allowed state → ∀ client →
        stopLoss (claims state client) (receivedCollateral mta paid state client) ≤ᵣ rat (mta client)
      broker-within-tolerance : ∀ state → Allowed state →
        Credit.brokerResidual (claims state) (receivedCollateral mta paid state) ≤ᵣ totalTolerance mta
      all-severities-within-tolerance : (severity : State → Credit.Severity clients) →
        ∀ state → Allowed state →
        Credit.realizedCloseoutLoss (claims state) (receivedCollateral mta paid state) (severity state)
          ≤ᵣ totalTolerance mta
  open CallGuarantee public

  call-policy-correct : ∀ mta → NonnegativePayments mta → ∀ paid → NonnegativePayments paid →
    CallGuarantee mta paid
  call-policy-correct mta mta₊ paid paid₊ .requests-valid = requested-nonnegative mta paid
  call-policy-correct mta mta₊ paid paid₊ .received-balances-valid = received-nonnegative mta paid paid₊
  call-policy-correct mta mta₊ paid paid₊ .clients-within-tolerance = client-residual-bound mta mta₊ paid
  call-policy-correct mta mta₊ paid paid₊ .broker-within-tolerance = broker-residual-bound mta mta₊ paid
  call-policy-correct mta mta₊ paid paid₊ .all-severities-within-tolerance = all-losses-bound mta mta₊ paid

  zeroMTA : Payments
  zeroMTA client = 0

  zero-mta-full-coverage : ∀ paid state → Allowed state → ∀ client →
    claims state client ≤ᵣ receivedCollateral zeroMTA paid state client
  zero-mta-full-coverage paid state member client = isTrans≤≡ᵣ _ _ _
    (coverage-with-tolerance zeroMTA (λ _ → ℚ.decℚ≤?) paid state member client)
    (+IdR (receivedCollateral zeroMTA paid state client))

  zero-mta-residual-zero : ∀ paid state → Allowed state →
    Credit.brokerResidual (claims state) (receivedCollateral zeroMTA paid state) ≡ 0
  zero-mta-residual-zero paid state member = sum-cong _ (λ _ → 0)
    (λ client → stopLoss-zero-below _ _ (zero-mta-full-coverage paid state member client))
    ∙ sum-zero clients

  zero-mta-all-losses-zero : ∀ paid → (severity : State → Credit.Severity clients) →
    ∀ state → Allowed state →
    Credit.realizedCloseoutLoss (claims state) (receivedCollateral zeroMTA paid state) (severity state) ≡ 0
  zero-mta-all-losses-zero paid severity state member =
    Credit.covered-loss-zero (claims state) (receivedCollateral zeroMTA paid state) (severity state)
      (zero-mta-full-coverage paid state member)

-- An optional adapter from exact least-margin certificates. None of the
-- tolerance or zero-MTA results depends on this stronger exactness input.
module CertifiedMinimumTransfer {clients : ℕ} {State : Type₀}
  (Allowed : State → Type₀) (claims collateral : State → Vector clients)
  (requirements : Fin clients → ℚ)
  (certificates : ∀ client → MarginCertificate Allowed
    (λ state → claims state client) (λ state → collateral state client) (rat (requirements client))) where
  open MinimumTransfer Allowed claims collateral requirements
    (λ client → ≤ᵣ→≤ℚ 0 (requirements client) (certificate-nonnegative (certificates client)))
    (λ state member client → certificate-coverage (certificates client) state member) public
