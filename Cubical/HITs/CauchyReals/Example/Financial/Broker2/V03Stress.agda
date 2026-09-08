{-# OPTIONS --safe --cubical #-}

-- Version 3: the same client engine must survive every supplied stress.
-- Scenarios are nonempty and finite; their numerical values remain arbitrary
-- Cauchy reals. Eligible collateral excludes the separately recorded cash.
module Cubical.HITs.CauchyReals.Example.Financial.Broker2.V03Stress where

open import Cubical.HITs.CauchyReals.Example.Financial.Core.Finite public
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.Shortfall
import Cubical.HITs.CauchyReals.Example.Financial.Broker2.V02Clients as Previous
import Cubical.HITs.CauchyReals.Example.Financial.Margin.Base as Margin
import Cubical.HITs.CauchyReals.Example.Financial.Risk.WorstCase as Worst
import Cubical.HITs.CauchyReals.Example.Financial.Margin.CounterpartyRisk as Credit

open Previous using (Nonnegative) public

record Market (clients stresses : ℕ) : Type₀ where
  constructor market-data
  field
    claims collateral : Fin (suc stresses) → Vector clients
    collateral-nonnegative : ∀ scenario → Nonnegative (collateral scenario)
open Market public

record State (clients stresses : ℕ) : Type₀ where
  constructor state
  field
    market : Market clients stresses
    cash : Vector clients
    cash-nonnegative : Nonnegative cash
open State public

view : ∀ {clients stresses} → State clients stresses → Fin (suc stresses) → Previous.State clients
view b scenario = Previous.state (claims (market b) scenario)
  (λ client → collateral (market b) scenario client +ᵣ cash b client)
  (λ client → nonnegative-add _ _ (collateral-nonnegative (market b) scenario client)
    (cash-nonnegative b client))

Safe : ∀ {clients stresses} → State clients stresses → Type₀
Safe b = ∀ scenario → Previous.Safe (view b scenario)

scenarioClaims scenarioCollateral : ∀ {clients stresses} → State clients stresses → Fin clients → Vector (suc stresses)
scenarioClaims b client scenario = Previous.claims (view b scenario) client
scenarioCollateral b client scenario = Previous.cash (view b scenario) client

-- An INCREMENTAL call: existing cash is already included in view.
quoteCall : ∀ {clients stresses} → State clients stresses → Vector clients
quoteCall b client = Margin.requiredMargin (scenarioClaims b client) (scenarioCollateral b client)

quote-nonnegative : ∀ {clients stresses} (b : State clients stresses) → Nonnegative (quoteCall b)
quote-nonnegative b client = Margin.requiredMargin-nonnegative (scenarioClaims b client) (scenarioCollateral b client)

receive : ∀ {clients stresses} → State clients stresses → (paid : Vector clients) →
  Nonnegative paid → State clients stresses
receive b paid paid₊ = state (market b) (λ client → cash b client +ᵣ paid client)
  (λ client → nonnegative-add _ _ (cash-nonnegative b client) (paid₊ client))

receive-correct : ∀ {clients stresses} (b : State clients stresses) paid paid₊ →
  (∀ client → quoteCall b client ≤ᵣ paid client) → Safe (receive b paid paid₊)
receive-correct b paid paid₊ enough scenario client = isTrans≤≡ᵣ _ _ _
  (Margin.margin-bound→coverage (scenarioClaims b client) (scenarioCollateral b client) (paid client) (enough client) scenario)
  (sym (+ᵣAssoc (collateral (market b) scenario client) (cash b client) (paid client)))

quote-least : ∀ {clients stresses} (b : State clients stresses) paid paid₊ →
  Safe (receive b paid paid₊) → ∀ client → quoteCall b client ≤ᵣ paid client
quote-least b paid paid₊ safe client = Margin.margin-least (scenarioClaims b client) (scenarioCollateral b client) (paid client) (paid₊ client)
  (λ scenario → isTrans≤≡ᵣ _ _ _ (safe scenario client)
    (+ᵣAssoc (collateral (market b) scenario client) (cash b client) (paid client)))

quote-sufficient : ∀ {clients stresses} (b : State clients stresses) →
  Safe (receive b (quoteCall b) (quote-nonnegative b))
quote-sufficient b = receive-correct b (quoteCall b) (quote-nonnegative b)
  (λ client → ≤ᵣ-refl (quoteCall b client))

remaining-quote : ∀ {clients stresses} (b : State clients stresses) paid paid₊ client →
  quoteCall (receive b paid paid₊) client ≡ stopLoss (quoteCall b client) (paid client)
remaining-quote b paid paid₊ client =
  cong (Margin.requiredMargin (λ scenario → claims (market b) scenario client))
    (funExt (λ scenario → +ᵣAssoc (collateral (market b) scenario client) (cash b client) (paid client)))
  ∙ Margin.margin-postCash (scenarioClaims b client) (scenarioCollateral b client) (paid client) (paid₊ client)

residual : ∀ {clients stresses} → State clients stresses → Fin (suc stresses) → ℝ
residual b scenario = Previous.residual (view b scenario)

loss : ∀ {clients stresses} → State clients stresses → Fin (suc stresses) → Credit.Severity clients → ℝ
loss b scenario = Previous.loss (view b scenario)

safe-residual-zero : ∀ {clients stresses} (b : State clients stresses) → Safe b → ∀ scenario → residual b scenario ≡ 0
safe-residual-zero b safe scenario = Previous.safe-residual-zero (view b scenario) (safe scenario)

safe-loss-zero : ∀ {clients stresses} (b : State clients stresses) → Safe b →
  ∀ scenario severity → loss b scenario severity ≡ 0
safe-loss-zero b safe scenario = Previous.safe-loss-zero (view b scenario) (safe scenario)

-- Refinement: receipt behavior agrees in EVERY snapshot; the uniform quote
-- dominates each snapshot quote. It equals V02's quote for a singleton market.
receive-refines-V02 : ∀ {clients stresses} (b : State clients stresses) paid paid₊ scenario →
  view (receive b paid paid₊) scenario ≡ Previous.receive (view b scenario) paid paid₊
receive-refines-V02 b paid paid₊ scenario = Previous.state-path _ _ refl
  (funExt (λ client → +ᵣAssoc (collateral (market b) scenario client) (cash b client) (paid client)))

snapshot-quote≤uniform : ∀ {clients stresses} (b : State clients stresses) scenario client →
  Previous.quoteCall (view b scenario) client ≤ᵣ quoteCall b client
snapshot-quote≤uniform b scenario client = Worst.worstCase-upper (λ s → stopLoss (scenarioClaims b client s) (scenarioCollateral b client s)) scenario

singleton : ∀ {clients} → Previous.State clients → State clients 0
singleton b = state (market-data (λ _ → Previous.claims b) (λ _ _ → 0) (λ _ _ → ≤ᵣ-refl 0))
  (Previous.cash b) (Previous.cash-nonnegative b)

singleton-quote-refines-V02 : ∀ {clients} (b : Previous.State clients) →
  quoteCall (singleton b) ≡ Previous.quoteCall b
singleton-quote-refines-V02 b = funExt (λ client →
  cong (stopLoss (Previous.claims b client)) (+IdL (Previous.cash b client)))

state-path : ∀ {clients stresses} (left right : State clients stresses) →
  market left ≡ market right → cash left ≡ cash right → left ≡ right
state-path left right markets balances i .market = markets i
state-path left right markets balances i .cash = balances i
state-path left right markets balances i .cash-nonnegative client =
  isProp→PathP (λ j → isProp≤ᵣ 0 (balances j client))
    (cash-nonnegative left client) (cash-nonnegative right client) i
