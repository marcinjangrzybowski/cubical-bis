{-# OPTIONS --safe --cubical #-}

-- Uniform revaluation reserves for claims and effective collateral.
-- Literature motivation: REFERENCES.md#bcbs-fx-2013 and
-- REFERENCES.md#brigo-pallavicini-2014. Drift bounds are supplied model
-- assumptions, not inferred forecasts or regulatory calibration.
module Cubical.HITs.CauchyReals.Example.Financial.Broker.Stage06Revaluation where

open import Cubical.HITs.CauchyReals.Example.Financial.Core.Finite
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.Shortfall
import Cubical.HITs.CauchyReals.Example.Financial.Margin.CounterpartyRisk as Credit
open import Cubical.Tactics.CommRingSolver.Specialised.Reals

module Revaluation {clients : ℕ} {State : Type₀} (Allowed : State → Type₀) where

  Profile : Type₀
  Profile = State → Vector clients

  creditCash : Profile → Vector clients → Profile
  creditCash C cash state client = C state client +ᵣ cash client

  CashCoverage : Profile → Profile → Vector clients → Type₀
  CashCoverage X C cash = ∀ state → Allowed state →
    ∀ client → X state client ≤ᵣ creditCash C cash state client

  -- The scenario and client labels are preserved across snapshots. Existing
  -- credited cash is kept separate from the collateral profile whose value
  -- changes; these bounds do not justify withdrawals or collateral reuse.
  record DriftBounds (oldClaims oldCollateral newClaims newCollateral : Profile) : Type₀ where
    field
      claimShock collateralDrop : Vector clients
      claimShock-nonnegative : ∀ client → 0 ≤ᵣ claimShock client
      collateralDrop-nonnegative : ∀ client → 0 ≤ᵣ collateralDrop client
      claim-rise : ∀ state → Allowed state → ∀ client →
        newClaims state client ≤ᵣ oldClaims state client +ᵣ claimShock client
      collateral-fall : ∀ state → Allowed state → ∀ client →
        oldCollateral state client ≤ᵣ newCollateral state client +ᵣ collateralDrop client
  open DriftBounds public

  driftReserve : ∀ {X C Y D} → DriftBounds X C Y D → Vector clients
  driftReserve drift client = claimShock drift client +ᵣ collateralDrop drift client

  driftReserve-nonnegative : ∀ {X C Y D} (drift : DriftBounds X C Y D) client →
    0 ≤ᵣ driftReserve drift client
  driftReserve-nonnegative drift client = nonnegative-add _ _
    (claimShock-nonnegative drift client) (collateralDrop-nonnegative drift client)

  protectedCash : ∀ {X C Y D} → Vector clients → DriftBounds X C Y D → Vector clients
  protectedCash cash drift client = cash client +ᵣ driftReserve drift client

  protectedCash-nonnegative : ∀ {X C Y D} cash (drift : DriftBounds X C Y D) →
    (∀ client → 0 ≤ᵣ cash client) → ∀ client → 0 ≤ᵣ protectedCash cash drift client
  protectedCash-nonnegative cash drift cash₊ client =
    nonnegative-add _ _ (cash₊ client) (driftReserve-nonnegative drift client)

  -- A sufficient old cash requirement remains sufficient after adding the
  -- claim-rise and collateral-fall reserves. This statement also applies to
  -- conservative requirements; it makes no leastness claim.
  revaluation-covers : ∀ {X C Y D} (drift : DriftBounds X C Y D) cash →
    CashCoverage X C cash → CashCoverage Y D (protectedCash cash drift)
  revaluation-covers {C = C} {D = D} drift cash covered state member client =
    isTrans≤ᵣ _ _ _ (claim-rise drift state member client)
      (isTrans≤ᵣ _ _ _
        (≤ᵣ-+o _ _ (claimShock drift client) (covered state member client))
        (isTrans≤≡ᵣ _ _ _
          (≤ᵣ-+o _ _ (claimShock drift client)
            (≤ᵣ-+o _ _ (cash client) (collateral-fall drift state member client))) regroup))
    where
    regroup : ((D state client +ᵣ collateralDrop drift client) +ᵣ cash client)
      +ᵣ claimShock drift client ≡ D state client +ᵣ protectedCash cash drift client
    regroup = ℝ!

  -- Before any reserve is paid, the existing covered cash still limits the
  -- new unsecured claim by the reserve. Calculating it does not credit it.
  drift-client-residual : ∀ {X C Y D} (drift : DriftBounds X C Y D) cash →
    CashCoverage X C cash → ∀ state → Allowed state → ∀ client →
    stopLoss (Y state client) (creditCash D cash state client) ≤ᵣ driftReserve drift client
  drift-client-residual {D = D} drift cash covered state member client =
    stopLoss-upper _ _ _ (driftReserve-nonnegative drift client)
      (isTrans≤≡ᵣ _ _ _ (revaluation-covers drift cash covered state member client)
        (+ᵣAssoc (D state client) (cash client) (driftReserve drift client)))

  drift-broker-residual : ∀ {X C Y D} (drift : DriftBounds X C Y D) cash →
    CashCoverage X C cash → ∀ state → Allowed state →
    Credit.brokerResidual (Y state) (creditCash D cash state) ≤ᵣ sum (driftReserve drift)
  drift-broker-residual {Y = Y} {D = D} drift cash covered state member =
    Credit.residual-budget (Y state) (creditCash D cash state) (driftReserve drift)
      (drift-client-residual drift cash covered state member)

  drift-all-losses : ∀ {X C Y D} (drift : DriftBounds X C Y D) cash →
    CashCoverage X C cash → (severity : State → Credit.Severity clients) →
    ∀ state → Allowed state →
    Credit.realizedCloseoutLoss (Y state) (creditCash D cash state) (severity state)
      ≤ᵣ sum (driftReserve drift)
  drift-all-losses {Y = Y} {D = D} drift cash covered severity state member =
    isTrans≤ᵣ _ _ _ (Credit.loss≤brokerResidual (Y state) (creditCash D cash state) (severity state))
      (drift-broker-residual drift cash covered state member)

  -- These zero-loss results are conditional on protectedCash actually
  -- being available. They do not treat the generated reserve as a receipt.
  protected-residual-zero : ∀ {X C Y D} (drift : DriftBounds X C Y D) cash →
    CashCoverage X C cash → ∀ state → Allowed state →
    Credit.brokerResidual (Y state) (creditCash D (protectedCash cash drift) state) ≡ 0
  protected-residual-zero {Y = Y} {D = D} drift cash covered state member =
    sum-cong _ (λ _ → 0)
      (λ client → stopLoss-zero-below _ _ (revaluation-covers drift cash covered state member client))
      ∙ sum-zero clients

  protected-all-losses-zero : ∀ {X C Y D} (drift : DriftBounds X C Y D) cash →
    CashCoverage X C cash → (severity : State → Credit.Severity clients) →
    ∀ state → Allowed state →
    Credit.realizedCloseoutLoss (Y state) (creditCash D (protectedCash cash drift) state)
      (severity state) ≡ 0
  protected-all-losses-zero {Y = Y} {D = D} drift cash covered severity state member =
    Credit.covered-loss-zero (Y state) (creditCash D (protectedCash cash drift) state)
      (severity state) (revaluation-covers drift cash covered state member)

  -- Composition can be iterated across any supplied finite sequence of
  -- snapshot changes on the same domain. No independence of shocks is used.
  compose-drift : ∀ {X C Y D Z E} → DriftBounds X C Y D → DriftBounds Y D Z E → DriftBounds X C Z E
  compose-drift first second .claimShock client = claimShock first client +ᵣ claimShock second client
  compose-drift first second .collateralDrop client =
    collateralDrop first client +ᵣ collateralDrop second client
  compose-drift first second .claimShock-nonnegative client = nonnegative-add _ _
    (claimShock-nonnegative first client) (claimShock-nonnegative second client)
  compose-drift first second .collateralDrop-nonnegative client = nonnegative-add _ _
    (collateralDrop-nonnegative first client) (collateralDrop-nonnegative second client)
  compose-drift {X = X} first second .claim-rise state member client = isTrans≤ᵣ _ _ _
    (claim-rise second state member client)
    (isTrans≤≡ᵣ _ _ _
      (≤ᵣ-+o _ _ (claimShock second client) (claim-rise first state member client))
      (sym (+ᵣAssoc (X state client) (claimShock first client) (claimShock second client))))
  compose-drift {E = E} first second .collateral-fall state member client = isTrans≤ᵣ _ _ _
    (collateral-fall first state member client)
    (isTrans≤≡ᵣ _ _ _
      (≤ᵣ-+o _ _ (collateralDrop first client) (collateral-fall second state member client)) regroup)
    where
    regroup : (E state client +ᵣ collateralDrop second client) +ᵣ collateralDrop first client
      ≡ E state client +ᵣ (collateralDrop first client +ᵣ collateralDrop second client)
    regroup = ℝ!

  composed-reserve : ∀ {X C Y D Z E} (first : DriftBounds X C Y D) (second : DriftBounds Y D Z E) →
    driftReserve (compose-drift first second) ≡ (λ client → driftReserve first client +ᵣ driftReserve second client)
  composed-reserve first second = funExt (λ client → ℝ!)
