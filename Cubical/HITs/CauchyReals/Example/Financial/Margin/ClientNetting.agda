module Cubical.HITs.CauchyReals.Example.Financial.Margin.ClientNetting where

open import Cubical.HITs.CauchyReals.Example.Financial.Core.Finite public
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.Shortfall
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.FiniteShortfall using (positivePart-sum-bound) public
import Cubical.HITs.CauchyReals.Example.Financial.Risk.FiniteShortfall as FS
open import Cubical.HITs.CauchyReals.Example.Financial.Core.EconomicEquivalence
open import Cubical.HITs.CauchyReals.Algebra.Order.Properties using (isIrrefl<ᵣ)
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
import Cubical.Data.FinData.Base as F

-- A coordinate is a SUPPLIED authorized netting set. Its positive claim
-- is owed to the broker; its negative claim is owed by the broker. These
-- tags are mathematical input, not evidence of legal enforceability.
-- Opposite signs at different coordinates must not cancel in exposure.
-- Positive residual claims are exposure, not a model of realized default
-- losses or of the cash needed to settle the broker's outgoing payments.
separateExposure : ∀ {clients} → Vector clients → ℝ
separateExposure claims = sum (λ i → positivePart (claims i))

brokerResidual : ∀ {clients} → Vector clients → Vector clients → ℝ
brokerResidual claims collateral = sum (λ i → stopLoss (claims i) (collateral i))

-- Pooling all marks/collateral is a comparison quantity. It is not declared
-- to be the broker's residual when the coordinates are different netting sets.
pooledResidual : ∀ {clients} → Vector clients → Vector clients → ℝ
pooledResidual claims collateral = stopLoss (sum claims) (sum collateral)

separateExposure-nonnegative : ∀ {clients} (claims : Vector clients) →
  0 ≤ᵣ separateExposure claims
separateExposure-nonnegative claims = sum-nonnegative
  (λ i → positivePart (claims i)) (λ i → positivePart-nonnegative (claims i))

brokerResidual-nonnegative : ∀ {clients} (claims collateral : Vector clients) →
  0 ≤ᵣ brokerResidual claims collateral
brokerResidual-nonnegative claims collateral = sum-nonnegative
  (λ i → stopLoss (claims i) (collateral i))
  (λ i → stopLoss-nonnegative (claims i) (collateral i))

private
  difference-zero : ∀ x → x -ᵣ 0 ≡ x
  difference-zero x = ℝ!

brokerResidual-no-collateral : ∀ {clients} (claims : Vector clients) →
  brokerResidual claims (λ _ → 0) ≡ separateExposure claims
brokerResidual-no-collateral claims = sum-cong
  (λ i → stopLoss (claims i) 0) (λ i → positivePart (claims i))
  (λ i → cong positivePart (difference-zero (claims i)))

pooled-stopLoss-bound : ∀ {clients} (claims collateral : Vector clients) →
  pooledResidual claims collateral ≤ᵣ brokerResidual claims collateral
pooled-stopLoss-bound = FS.stopLoss-sum-bound

brokerResidual-claims-monotone : ∀ {clients} (X Y collateral : Vector clients) →
  (∀ i → X i ≤ᵣ Y i) → brokerResidual X collateral ≤ᵣ brokerResidual Y collateral
brokerResidual-claims-monotone X Y collateral bound = sum-monotone
  (λ i → stopLoss (X i) (collateral i)) (λ i → stopLoss (Y i) (collateral i))
  (λ i → stopLoss-monotone (X i) (Y i) (collateral i) (bound i))

brokerResidual-collateral-antitone : ∀ {clients} (claims C D : Vector clients) →
  (∀ i → C i ≤ᵣ D i) → brokerResidual claims D ≤ᵣ brokerResidual claims C
brokerResidual-collateral-antitone claims C D bound = sum-monotone
  (λ i → stopLoss (claims i) (D i)) (λ i → stopLoss (claims i) (C i))
  (λ i → stopLoss-antitone-threshold (claims i) (C i) (D i) (bound i))

-- Bounds must be discharged separately for each client netting set.
residual-budget : ∀ {clients} (claims collateral reserves : Vector clients) →
  (∀ i → stopLoss (claims i) (collateral i) ≤ᵣ reserves i) →
  brokerResidual claims collateral ≤ᵣ sum reserves
residual-budget claims collateral reserves =
  sum-monotone (λ i → stopLoss (claims i) (collateral i)) reserves

residual-covered-by-reserve : ∀ claim collateral reserve →
  0 ≤ᵣ reserve → claim ≤ᵣ collateral +ᵣ reserve →
  stopLoss claim collateral ≤ᵣ reserve
residual-covered-by-reserve = stopLoss-upper

record CashAmounts (clients : ℕ) : Type₀ where
  constructor cash-amounts
  field
    amounts : Vector clients
    cash-nonnegative : ∀ i → 0 ≤ᵣ amounts i
open CashAmounts public

-- Cash collateral and supplementary reserves are valued in the same units
-- and horizon as claims. Funding, custody, and recovery are model inputs;
-- a nonnegative cash vector is not itself a proof of their availability.
cash-reserves-cover-broker : ∀ {clients} (claims : Vector clients)
  (collateral reserves : CashAmounts clients) →
  (∀ i → claims i ≤ᵣ amounts collateral i +ᵣ amounts reserves i) →
  brokerResidual claims (amounts collateral) ≤ᵣ sum (amounts reserves)
cash-reserves-cover-broker claims collateral reserves covered = residual-budget
  claims (amounts collateral) (amounts reserves)
  (λ i → residual-covered-by-reserve (claims i) (amounts collateral i)
    (amounts reserves i) (cash-nonnegative reserves i) (covered i))

-- Combining two books adds positions WITHIN each common authorized label.
-- Collateral is added at that same label; there is no cross-client offset.
-- Additive collateral inputs do not certify availability or prevent reuse
-- of the same physical collateral by an external bookkeeping system.
brokerResidual-subadditive : ∀ {clients} (X Y C D : Vector clients) →
  brokerResidual (λ i → X i +ᵣ Y i) (λ i → C i +ᵣ D i)
    ≤ᵣ brokerResidual X C +ᵣ brokerResidual Y D
brokerResidual-subadditive X Y C D = isTrans≤≡ᵣ _ _ _
  (sum-monotone
    (λ i → stopLoss (X i +ᵣ Y i) (C i +ᵣ D i))
    (λ i → stopLoss (X i) (C i) +ᵣ stopLoss (Y i) (D i))
    (λ i → stopLoss-subadditive (X i) (Y i) (C i) (D i)))
  (sum-add (λ i → stopLoss (X i) (C i)) (λ i → stopLoss (Y i) (D i)))

-- The outer index fixes the netting sets; the inner index lists their trades.
-- This comparison permits pooling only within the explicitly supplied sets.
groupedResidual : ∀ {clients trades} → (Fin clients → Vector trades) → Vector clients → ℝ
groupedResidual claims collateral = brokerResidual (λ i → sum (claims i)) collateral

within-set-netting-bound : ∀ {clients trades}
  (claims collateral : Fin clients → Vector trades) →
  groupedResidual claims (λ i → sum (collateral i))
    ≤ᵣ sum (λ i → brokerResidual (claims i) (collateral i))
within-set-netting-bound claims collateral = sum-monotone
  (λ i → pooledResidual (claims i) (collateral i))
  (λ i → brokerResidual (claims i) (collateral i))
  (λ i → pooled-stopLoss-bound (claims i) (collateral i))

-- Preserve BOTH the client netting-set label and the scenario label in
-- economic identity. Collateral is fixed here; varying it would require
-- including collateral in the profile used to define equivalence as well.
module ClientProfiles {clients scenarios : ℕ} (Position : Type₀)
  (claims : Position → Fin clients → Vector scenarios)
  (collateral : Fin clients → Vector scenarios) where

  module Classes = EconomicModel (Fin clients × Fin scenarios) Position
    (λ p label → claims p (fst label) (snd label))

  residualProfile : (Fin clients × Fin scenarios → ℝ) → Vector scenarios
  residualProfile profile ω = brokerResidual
    (λ i → profile (i , ω)) (λ i → collateral i ω)

  module Capital (ρ : Vector scenarios → ℝ) where
    module Descended = Classes.Risk (λ profile → ρ (residualProfile profile))
    open Descended public

    residual-risk-invariant : {p q : Position} → p Classes.≈ᴱ q →
      ρ (λ ω → brokerResidual (λ i → claims p i ω) (λ i → collateral i ω))
      ≡ ρ (λ ω → brokerResidual (λ i → claims q i ω) (λ i → collateral i ω))
    residual-risk-invariant = risk-invariant
