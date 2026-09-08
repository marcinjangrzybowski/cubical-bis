module Cubical.HITs.CauchyReals.Example.Financial.Instruments.FXSwap where

open import Cubical.HITs.CauchyReals.Example.Financial.Portfolio.Base public
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
import Cubical.Data.Nat.Order as N
import Cubical.Data.FinData.Base as F

-- Quotes are domestic units per foreign unit. Cashflows are positive when
-- RECEIVED BY THE BROKER. Currency coordinates are retained until valuation.
domestic foreign : Fin 2
domestic = F.zero
foreign = F.suc F.zero

data Leg : Type₀ where
  near far : Leg

record FXSwap : Type₀ where
  constructor fx-swap
  field
    signedForeign : ℝ
    nearRate farRate : ℝ
    near-positive : 0 <ᵣ nearRate
    far-positive : 0 <ᵣ farRate
    nearDate farDate : ℕ
    dates-ordered : nearDate N.< farDate
open FXSwap public

-- A positive signed notional means the client receives foreign principal
-- on the near date, then returns it on the far date. Negative reverses it.
cashflow : FXSwap → Leg → Vector 2
cashflow swap near F.zero = signedForeign swap ·ᵣ nearRate swap
cashflow swap near (F.suc F.zero) = -ᵣ signedForeign swap
cashflow swap far F.zero = -ᵣ (signedForeign swap ·ᵣ farRate swap)
cashflow swap far (F.suc F.zero) = signedForeign swap

settlementDate : FXSwap → Leg → ℕ
settlementDate swap near = nearDate swap
settlementDate swap far = farDate swap

reverseSwap : FXSwap → FXSwap
reverseSwap swap = record swap { signedForeign = -ᵣ signedForeign swap }

scaleSwap : ℝ → FXSwap → FXSwap
scaleSwap a swap = record swap { signedForeign = a ·ᵣ signedForeign swap }

reverse-cashflow : ∀ swap leg currency →
  cashflow (reverseSwap swap) leg currency ≡ -ᵣ cashflow swap leg currency
reverse-cashflow swap near F.zero = ℝ!
reverse-cashflow swap near (F.suc F.zero) = refl
reverse-cashflow swap far F.zero = ℝ!
reverse-cashflow swap far (F.suc F.zero) = refl

scale-cashflow : ∀ a swap leg currency →
  cashflow (scaleSwap a swap) leg currency ≡ a ·ᵣ cashflow swap leg currency
scale-cashflow a swap near F.zero = ℝ!
scale-cashflow a swap near (F.suc F.zero) = ℝ!
scale-cashflow a swap far F.zero = ℝ!
scale-cashflow a swap far (F.suc F.zero) = refl

-- These identities describe contracts, not permission to net payments
-- across different dates or counterparties.
foreign-principal-returned : ∀ swap →
  cashflow swap near foreign +ᵣ cashflow swap far foreign ≡ 0
foreign-principal-returned swap = ℝ!

domestic-swap-points : ∀ swap →
  cashflow swap near domestic +ᵣ cashflow swap far domestic
    ≡ signedForeign swap ·ᵣ (nearRate swap -ᵣ farRate swap)
domestic-swap-points swap = ℝ!

-- Discount factors are supplied effective valuation inputs for the given
-- settlement date. A foreign factor may reflect the chosen funding/basis
-- convention. This model does not derive a curve from interest rates.
record FXState : Type₀ where
  constructor fx-state
  field
    spot domesticDiscount foreignDiscount : ℝ
    spot-positive : 0 <ᵣ spot
    domesticDiscount-positive : 0 <ᵣ domesticDiscount
    foreignDiscount-positive : 0 <ᵣ foreignDiscount
open FXState public

valueCashflow : FXState → Vector 2 → ℝ
valueCashflow state flow = domesticDiscount state ·ᵣ flow domestic
  +ᵣ (spot state ·ᵣ foreignDiscount state) ·ᵣ flow foreign

legValue : FXSwap → Leg → FXState → ℝ
legValue swap leg state = valueCashflow state (cashflow swap leg)

-- The near leg has already settled when farValue is used as closeout mark.
-- Positive farValue is a replacement claim owed to the broker, not its
-- market loss. Broker market loss under a move is old mark minus new mark.
farValue : FXSwap → FXState → ℝ
farValue swap state = legValue swap far state

far-value-formula : ∀ swap state → farValue swap state
  ≡ signedForeign swap ·ᵣ
    (spot state ·ᵣ foreignDiscount state -ᵣ farRate swap ·ᵣ domesticDiscount state)
far-value-formula swap state = ℝ!

near-value-formula : ∀ swap state → legValue swap near state
  ≡ signedForeign swap ·ᵣ
    (nearRate swap ·ᵣ domesticDiscount state -ᵣ spot state ·ᵣ foreignDiscount state)
near-value-formula swap state = ℝ!

reverse-value : ∀ swap state → farValue (reverseSwap swap) state ≡ -ᵣ farValue swap state
reverse-value swap state = ℝ!

scale-value : ∀ a swap state → farValue (scaleSwap a swap) state ≡ a ·ᵣ farValue swap state
scale-value a swap state = ℝ!

par-far-value : ∀ swap state →
  spot state ·ᵣ foreignDiscount state ≡ farRate swap ·ᵣ domesticDiscount state →
  farValue swap state ≡ 0
par-far-value swap state par = far-value-formula swap state
  ∙ cong (λ u → signedForeign swap ·ᵣ (u -ᵣ farRate swap ·ᵣ domesticDiscount state)) par
  ∙ cong (signedForeign swap ·ᵣ_) (+-ᵣ _) ∙ Rℝ.0RightAnnihilates _

data Phase : Type₀ where
  beforeNear afterNear afterFar : Phase

remainingValue : Phase → FXSwap → (Leg → FXState) → ℝ
remainingValue beforeNear swap states = legValue swap near (states near) +ᵣ farValue swap (states far)
remainingValue afterNear swap states = farValue swap (states far)
remainingValue afterFar swap states = 0

near-settlement-removes-leg : ∀ swap states → remainingValue beforeNear swap states
  ≡ legValue swap near (states near) +ᵣ remainingValue afterNear swap states
near-settlement-removes-leg swap states = refl

-- Exact finite changes separate spot, effective foreign funding, their
-- interaction, and domestic discount risk. No derivative or approximation
-- drops the interaction term when both spot and foreign discount move.
value-change : ∀ swap old new → farValue swap new -ᵣ farValue swap old
  ≡ signedForeign swap ·ᵣ
    (foreignDiscount old ·ᵣ (spot new -ᵣ spot old)
      +ᵣ spot old ·ᵣ (foreignDiscount new -ᵣ foreignDiscount old)
      +ᵣ (spot new -ᵣ spot old) ·ᵣ (foreignDiscount new -ᵣ foreignDiscount old)
      -ᵣ farRate swap ·ᵣ (domesticDiscount new -ᵣ domesticDiscount old))
value-change swap old new = ℝ!

brokerMarketLoss : FXSwap → FXState → FXState → ℝ
brokerMarketLoss swap old new = farValue swap old -ᵣ farValue swap new

-- Different trades may have different settlement dates and hence different
-- discount inputs in the same scenario. The caller supplies each trade's
-- valuation inputs for its far date at the current valuation time;
-- quantities aggregate through the existing market API.
claimMarket : ∀ {m n} → (Fin m → FXSwap) → (Fin m → Fin n → FXState) → Market m n
claimMarket swaps states trade scenario = farValue (swaps trade) (states trade scenario)

clientClaim : ∀ {m n} → (Fin m → FXSwap) → (Fin m → Fin n → FXState) → Vector m → Vector n
clientClaim swaps states = portfolioLoss (claimMarket swaps states)

client-claim-add : ∀ {m n} swaps states (u v : Vector m) (i : Fin n) →
  clientClaim swaps states (λ a → u a +ᵣ v a) i
    ≡ clientClaim swaps states u i +ᵣ clientClaim swaps states v i
client-claim-add swaps states = portfolio-add (claimMarket swaps states)

client-claim-scale : ∀ {m n} swaps states a (u : Vector m) (i : Fin n) →
  clientClaim swaps states (λ j → a ·ᵣ u j) i ≡ a ·ᵣ clientClaim swaps states u i
client-claim-scale swaps states = portfolio-scale (claimMarket swaps states)
