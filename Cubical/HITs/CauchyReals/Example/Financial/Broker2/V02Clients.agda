{-# OPTIONS --safe --cubical #-}

-- Version 2: the SAME quote/receive engine, lifted to client netting sets.
-- The new theorem quantifies over every client and every loss severity.
module Cubical.HITs.CauchyReals.Example.Financial.Broker2.V02Clients where

open import Cubical.HITs.CauchyReals.Example.Financial.Core.Finite public
import Cubical.HITs.CauchyReals.Example.Financial.Broker2.V01Account as Previous
import Cubical.HITs.CauchyReals.Example.Financial.Margin.CounterpartyRisk as Credit
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.Shortfall

Nonnegative : ∀ {clients} → Vector clients → Type₀
Nonnegative amounts = ∀ client → 0 ≤ᵣ amounts client

record State (clients : ℕ) : Type₀ where
  constructor state
  field
    claims cash : Vector clients
    cash-nonnegative : Nonnegative cash
open State public

view : ∀ {clients} → State clients → Fin clients → Previous.State
view b client = Previous.account (claims b client) (cash b client) (cash-nonnegative b client)

Safe : ∀ {clients} → State clients → Type₀
Safe b = ∀ client → Previous.Safe (view b client)

quoteCall : ∀ {clients} → State clients → Vector clients
quoteCall b client = Previous.quoteCall (view b client)

quote-nonnegative : ∀ {clients} (b : State clients) → Nonnegative (quoteCall b)
quote-nonnegative b client = Previous.quote-nonnegative (view b client)

receive : ∀ {clients} → State clients → (paid : Vector clients) → Nonnegative paid → State clients
receive b paid paid₊ = state (claims b) (λ client → cash b client +ᵣ paid client)
  (λ client → nonnegative-add _ _ (cash-nonnegative b client) (paid₊ client))

receive-correct : ∀ {clients} (b : State clients) paid paid₊ →
  (∀ client → quoteCall b client ≤ᵣ paid client) → Safe (receive b paid paid₊)
receive-correct b paid paid₊ enough client =
  Previous.receive-correct (view b client) (paid client) (paid₊ client) (enough client)

quote-least : ∀ {clients} (b : State clients) paid paid₊ →
  Safe (receive b paid paid₊) → ∀ client → quoteCall b client ≤ᵣ paid client
quote-least b paid paid₊ safe client =
  Previous.quote-least (view b client) (paid client) (paid₊ client) (safe client)

quote-sufficient : ∀ {clients} (b : State clients) → Safe (receive b (quoteCall b) (quote-nonnegative b))
quote-sufficient b = receive-correct b (quoteCall b) (quote-nonnegative b)
  (λ client → ≤ᵣ-refl (quoteCall b client))

residual : ∀ {clients} → State clients → ℝ
residual b = Credit.brokerResidual (claims b) (cash b)

loss : ∀ {clients} → State clients → Credit.Severity clients → ℝ
loss b = Credit.realizedCloseoutLoss (claims b) (cash b)

safe-residual-zero : ∀ {clients} (b : State clients) → Safe b → residual b ≡ 0
safe-residual-zero {clients} b safe = sum-cong _ (λ _ → 0)
  (λ client → stopLoss-zero-below _ _ (safe client)) ∙ sum-zero clients

safe-loss-zero : ∀ {clients} (b : State clients) → Safe b → ∀ severity → loss b severity ≡ 0
safe-loss-zero b safe θ = Credit.covered-loss-zero (claims b) (cash b) θ safe

-- Refinement: viewing any one client commutes with both engine operations.
quote-refines-V01 : ∀ {clients} (b : State clients) client →
  quoteCall b client ≡ Previous.quoteCall (view b client)
quote-refines-V01 b client = refl

receive-refines-V01 : ∀ {clients} (b : State clients) paid paid₊ client →
  view (receive b paid paid₊) client ≡ Previous.receive (view b client) (paid client) (paid₊ client)
receive-refines-V01 b paid paid₊ client = refl

-- Equal economic fields give equal proof-bearing book states.
state-path : ∀ {clients} (left right : State clients) → claims left ≡ claims right →
  cash left ≡ cash right → left ≡ right
state-path left right marks balances i .claims = marks i
state-path left right marks balances i .cash = balances i
state-path left right marks balances i .cash-nonnegative client =
  isProp→PathP (λ j → isProp≤ᵣ 0 (balances j client))
    (cash-nonnegative left client) (cash-nonnegative right client) i
