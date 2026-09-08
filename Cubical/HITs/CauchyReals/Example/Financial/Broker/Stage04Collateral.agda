{-# OPTIONS --safe --cubical #-}

module Cubical.HITs.CauchyReals.Example.Financial.Broker.Stage04Collateral where

open import Cubical.HITs.CauchyReals.Example.Financial.Core.Finite
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.Shortfall
  using (positivePart; positivePart-upper)
open import Cubical.Foundations.Equiv using (_≃_; propBiimpl→Equiv)
open import Cubical.Foundations.Univalence using (ua)

-- Inventory backing, eligibility and conservative collateral valuation:
-- REFERENCES.md#bcbs-fx-2013 and REFERENCES.md#bcbs-iosco-2020.
-- These are arithmetic guarantees conditional on supplied inventory and
-- client netting-set labels. They do not establish custody, legal rights,
-- regulatory compliance, or availability of collateral for settlement.

-- One inventory amount backs ALL client assignments of an asset. The asset
-- labels must represent distinct supplied inventory pools; representing the
-- same physical inventory twice under different labels is not verified here.
record CollateralAllocation (clients assets : ℕ) : Type₀ where
  field
    inventory : Vector assets
    inventory-nonnegative : ∀ asset → 0 ≤ᵣ inventory asset
    clientUnits : Fin clients → Vector assets
    units-nonnegative : ∀ client asset → 0 ≤ᵣ clientUnits client asset
    inventory-bound : ∀ asset →
      sum (λ client → clientUnits client asset) ≤ᵣ inventory asset
open CollateralAllocation public

-- A price includes conversion to the common unit of account. Retention is
-- the fraction remaining AFTER the haircut, including zero for an ineligible
-- asset. Prices and eligibility may move together with the scenario. Both
-- are inputs; no independent movements or market-data calibration is assumed.
record CollateralValuation (State : Type₀) (clients assets : ℕ) : Type₀ where
  field
    prices : State → Vector assets
    prices-nonnegative : ∀ state asset → 0 ≤ᵣ prices state asset
    retention : State → Fin clients → Vector assets
    retention-nonnegative : ∀ state client asset → 0 ≤ᵣ retention state client asset
    retention-at-most-one : ∀ state client asset → retention state client asset ≤ᵣ 1
open CollateralValuation public

allocatedUnits : ∀ {clients assets} → CollateralAllocation clients assets → Vector assets
allocatedUnits allocation asset = sum (λ client → clientUnits allocation client asset)

eligibleUnits : ∀ {State clients assets} → CollateralAllocation clients assets →
  CollateralValuation State clients assets → State → Fin clients → Vector assets
eligibleUnits allocation valuation state client asset =
  retention valuation state client asset ·ᵣ clientUnits allocation client asset

marketValue eligibleValue : ∀ {State clients assets} → CollateralAllocation clients assets →
  CollateralValuation State clients assets → State → Vector clients
marketValue allocation valuation state client =
  dot (prices valuation state) (clientUnits allocation client)
eligibleValue allocation valuation state client =
  dot (prices valuation state) (eligibleUnits allocation valuation state client)

inventoryValue : ∀ {State clients assets} → CollateralAllocation clients assets →
  CollateralValuation State clients assets → State → ℝ
inventoryValue allocation valuation state = dot (prices valuation state) (inventory allocation)

eligible-units-nonnegative : ∀ {State clients assets}
  (allocation : CollateralAllocation clients assets)
  (valuation : CollateralValuation State clients assets) state client asset →
  0 ≤ᵣ eligibleUnits allocation valuation state client asset
eligible-units-nonnegative allocation valuation state client asset = nonnegative-mul
  (retention valuation state client asset) (clientUnits allocation client asset)
  (retention-nonnegative valuation state client asset) (units-nonnegative allocation client asset)

eligible-units≤assigned : ∀ {State clients assets}
  (allocation : CollateralAllocation clients assets)
  (valuation : CollateralValuation State clients assets) state client asset →
  eligibleUnits allocation valuation state client asset ≤ᵣ clientUnits allocation client asset
eligible-units≤assigned allocation valuation state client asset = isTrans≤≡ᵣ _ _ _
  (≤ᵣ-·ᵣo (retention valuation state client asset) 1 (clientUnits allocation client asset)
    (units-nonnegative allocation client asset) (retention-at-most-one valuation state client asset))
  (·IdLᵣ (clientUnits allocation client asset))

market-nonnegative : ∀ {State clients assets}
  (allocation : CollateralAllocation clients assets)
  (valuation : CollateralValuation State clients assets) state client →
  0 ≤ᵣ marketValue allocation valuation state client
market-nonnegative allocation valuation state client = dot-nonnegative
  (prices valuation state) (clientUnits allocation client)
  (prices-nonnegative valuation state) (units-nonnegative allocation client)

eligible-nonnegative : ∀ {State clients assets}
  (allocation : CollateralAllocation clients assets)
  (valuation : CollateralValuation State clients assets) state client →
  0 ≤ᵣ eligibleValue allocation valuation state client
eligible-nonnegative allocation valuation state client = dot-nonnegative
  (prices valuation state) (eligibleUnits allocation valuation state client)
  (prices-nonnegative valuation state) (eligible-units-nonnegative allocation valuation state client)

inventory-value-nonnegative : ∀ {State clients assets}
  (allocation : CollateralAllocation clients assets)
  (valuation : CollateralValuation State clients assets) state →
  0 ≤ᵣ inventoryValue allocation valuation state
inventory-value-nonnegative allocation valuation state = dot-nonnegative
  (prices valuation state) (inventory allocation)
  (prices-nonnegative valuation state) (inventory-nonnegative allocation)

eligible≤market : ∀ {State clients assets}
  (allocation : CollateralAllocation clients assets)
  (valuation : CollateralValuation State clients assets) state client →
  eligibleValue allocation valuation state client ≤ᵣ marketValue allocation valuation state client
eligible≤market allocation valuation state client = dot-monotone
  (prices valuation state) (eligibleUnits allocation valuation state client) (clientUnits allocation client)
  (prices-nonnegative valuation state) (eligible-units≤assigned allocation valuation state client)

-- Exchange the finite asset and client sums, keeping every allocation in
-- the backing calculation. No ordering of real values or maximizer is used.
total-market-value : ∀ {State clients assets}
  (allocation : CollateralAllocation clients assets)
  (valuation : CollateralValuation State clients assets) state →
  sum (marketValue allocation valuation state)
    ≡ dot (prices valuation state) (allocatedUnits allocation)
total-market-value allocation valuation state =
  sum-exchange (λ client asset → prices valuation state asset ·ᵣ clientUnits allocation client asset)
  ∙ sum-cong
    (λ asset → sum (λ client → prices valuation state asset ·ᵣ clientUnits allocation client asset))
    (λ asset → prices valuation state asset ·ᵣ allocatedUnits allocation asset)
    (λ asset → sum-scale (prices valuation state asset) (λ client → clientUnits allocation client asset))

total-market≤inventory : ∀ {State clients assets}
  (allocation : CollateralAllocation clients assets)
  (valuation : CollateralValuation State clients assets) state →
  sum (marketValue allocation valuation state) ≤ᵣ inventoryValue allocation valuation state
total-market≤inventory allocation valuation state = isTrans≡≤ᵣ _ _ _
  (total-market-value allocation valuation state)
  (dot-monotone (prices valuation state) (allocatedUnits allocation) (inventory allocation)
    (prices-nonnegative valuation state) (inventory-bound allocation))

-- No modeled unit is credited to multiple clients beyond the supplied
-- asset inventory bound. This value inequality remains valid for any finite
-- numbers of clients and assets, including empty collections.
total-eligible≤inventory : ∀ {State clients assets}
  (allocation : CollateralAllocation clients assets)
  (valuation : CollateralValuation State clients assets) state →
  sum (eligibleValue allocation valuation state) ≤ᵣ inventoryValue allocation valuation state
total-eligible≤inventory allocation valuation state = isTrans≤ᵣ _ _ _
  (sum-monotone (eligibleValue allocation valuation state) (marketValue allocation valuation state)
    (eligible≤market allocation valuation state))
  (total-market≤inventory allocation valuation state)

-- Comparisons use the SAME scenario and client labels. In particular,
-- higher collateral prices are compared holding the claim profile fixed;
-- this does not assume that an FX-sensitive claim stays fixed as FX moves.
eligible-value-monotone : ∀ {State clients assets}
  (old new : CollateralAllocation clients assets)
  (oldValue newValue : CollateralValuation State clients assets) →
  (∀ client asset → clientUnits old client asset ≤ᵣ clientUnits new client asset) →
  (∀ state asset → prices oldValue state asset ≤ᵣ prices newValue state asset) →
  (∀ state client asset → retention oldValue state client asset ≤ᵣ retention newValue state client asset) →
  ∀ state client → eligibleValue old oldValue state client ≤ᵣ eligibleValue new newValue state client
eligible-value-monotone old new oldValue newValue unitsBound pricesBound retentionBound state client =
  sum-monotone
    (λ asset → prices oldValue state asset ·ᵣ eligibleUnits old oldValue state client asset)
    (λ asset → prices newValue state asset ·ᵣ eligibleUnits new newValue state client asset)
    (λ asset → ≤ᵣ₊Monotone·ᵣ
      (prices oldValue state asset) (prices newValue state asset)
      (eligibleUnits old oldValue state client asset) (eligibleUnits new newValue state client asset)
      (prices-nonnegative newValue state asset) (eligible-units-nonnegative old oldValue state client asset)
      (pricesBound state asset)
      (≤ᵣ₊Monotone·ᵣ
        (retention oldValue state client asset) (retention newValue state client asset)
        (clientUnits old client asset) (clientUnits new client asset)
        (retention-nonnegative newValue state client asset) (units-nonnegative old client asset)
        (retentionBound state client asset) (unitsBound client asset)))

Covered : ∀ {State clients assets} → (State → Type₀) →
  (State → Vector clients) → CollateralAllocation clients assets →
  CollateralValuation State clients assets → Type₀
Covered Allowed claims allocation valuation = ∀ state → Allowed state → ∀ client →
  claims state client ≤ᵣ eligibleValue allocation valuation state client

covered-isProp : ∀ {State clients assets} (Allowed : State → Type₀)
  (claims : State → Vector clients) (allocation : CollateralAllocation clients assets)
  (valuation : CollateralValuation State clients assets) →
  isProp (Covered Allowed claims allocation valuation)
covered-isProp Allowed claims allocation valuation = isPropΠ3 (λ _ _ _ → isProp≤ᵣ _ _)

covered-by-market : ∀ {State clients assets} (Allowed : State → Type₀)
  (claims : State → Vector clients) (allocation : CollateralAllocation clients assets)
  (valuation : CollateralValuation State clients assets) →
  Covered Allowed claims allocation valuation → ∀ state → Allowed state → ∀ client →
  claims state client ≤ᵣ marketValue allocation valuation state client
covered-by-market Allowed claims allocation valuation covered state member client =
  isTrans≤ᵣ _ _ _ (covered state member client) (eligible≤market allocation valuation state client)

-- The inventory backs the sum of POSITIVE client claims. Negative claims
-- at other client labels cannot cancel those exposures in this guarantee.
covered-positive-claims≤inventory : ∀ {State clients assets} (Allowed : State → Type₀)
  (claims : State → Vector clients) (allocation : CollateralAllocation clients assets)
  (valuation : CollateralValuation State clients assets) →
  Covered Allowed claims allocation valuation → ∀ state → Allowed state →
  sum (λ client → positivePart (claims state client)) ≤ᵣ inventoryValue allocation valuation state
covered-positive-claims≤inventory Allowed claims allocation valuation covered state member =
  isTrans≤ᵣ _ _ _
    (sum-monotone (λ client → positivePart (claims state client)) (eligibleValue allocation valuation state)
      (λ client → positivePart-upper (claims state client) (eligibleValue allocation valuation state client)
        (covered state member client) (eligible-nonnegative allocation valuation state client)))
    (total-eligible≤inventory allocation valuation state)

-- A substitution may change the asset vocabulary as well as the quantities.
-- Each side carries its own inventory backing. The replacement must preserve
-- the credited value of EACH client over the whole admitted scenario domain;
-- equality of a pooled collateral total alone is insufficient.
substitution-preserves-coverage : ∀ {State clients oldAssets newAssets}
  (Allowed : State → Type₀) (claims : State → Vector clients)
  (old : CollateralAllocation clients oldAssets) (oldValue : CollateralValuation State clients oldAssets)
  (new : CollateralAllocation clients newAssets) (newValue : CollateralValuation State clients newAssets) →
  (∀ state → Allowed state → ∀ client →
    eligibleValue old oldValue state client ≤ᵣ eligibleValue new newValue state client) →
  Covered Allowed claims old oldValue → Covered Allowed claims new newValue
substitution-preserves-coverage Allowed claims old oldValue new newValue dominates covered state member client =
  isTrans≤ᵣ _ _ _ (covered state member client) (dominates state member client)

-- This specializes substitution to conservative prices, retentions or
-- assigned quantities. Every proposed new allocation must still satisfy its
-- inventory constraint; an increase in credited amounts is not authorization
-- to reuse units already assigned to another client.
monotone-coverage : ∀ {State clients assets} (Allowed : State → Type₀)
  (claims : State → Vector clients) (old new : CollateralAllocation clients assets)
  (oldValue newValue : CollateralValuation State clients assets) →
  (∀ client asset → clientUnits old client asset ≤ᵣ clientUnits new client asset) →
  (∀ state asset → prices oldValue state asset ≤ᵣ prices newValue state asset) →
  (∀ state client asset → retention oldValue state client asset ≤ᵣ retention newValue state client asset) →
  Covered Allowed claims old oldValue → Covered Allowed claims new newValue
monotone-coverage Allowed claims old new oldValue newValue unitsBound pricesBound retentionBound =
  substitution-preserves-coverage Allowed claims old oldValue new newValue
    (λ state member client → eligible-value-monotone old new oldValue newValue
      unitsBound pricesBound retentionBound state client)

-- Equal eligible values identify the coverage propositions even when the
-- collateral representations use different asset types. They do not identify
-- the inventories, physical custody records, or other policies on those data.
equal-values≃coverage : ∀ {State clients oldAssets newAssets}
  (Allowed : State → Type₀) (claims : State → Vector clients)
  (old : CollateralAllocation clients oldAssets) (oldValue : CollateralValuation State clients oldAssets)
  (new : CollateralAllocation clients newAssets) (newValue : CollateralValuation State clients newAssets) →
  (∀ state → Allowed state → ∀ client →
    eligibleValue old oldValue state client ≡ eligibleValue new newValue state client) →
  Covered Allowed claims old oldValue ≃ Covered Allowed claims new newValue
equal-values≃coverage Allowed claims old oldValue new newValue equal = propBiimpl→Equiv
  (covered-isProp Allowed claims old oldValue) (covered-isProp Allowed claims new newValue)
  (substitution-preserves-coverage Allowed claims old oldValue new newValue
    (λ state member client → ≡ᵣWeaken≤ᵣ _ _ (equal state member client)))
  (substitution-preserves-coverage Allowed claims new newValue old oldValue
    (λ state member client → ≡ᵣWeaken≤ᵣ _ _ (sym (equal state member client))))

coverage-substitution-path : ∀ {State clients oldAssets newAssets}
  (Allowed : State → Type₀) (claims : State → Vector clients)
  (old : CollateralAllocation clients oldAssets) (oldValue : CollateralValuation State clients oldAssets)
  (new : CollateralAllocation clients newAssets) (newValue : CollateralValuation State clients newAssets) →
  (∀ state → Allowed state → ∀ client →
    eligibleValue old oldValue state client ≡ eligibleValue new newValue state client) →
  Covered Allowed claims old oldValue ≡ Covered Allowed claims new newValue
coverage-substitution-path Allowed claims old oldValue new newValue equal =
  ua (equal-values≃coverage Allowed claims old oldValue new newValue equal)
