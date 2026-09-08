{-# OPTIONS --safe --cubical #-}

module Cubical.HITs.CauchyReals.Example.Financial.Settlement.Base where

open import Cubical.HITs.CauchyReals.Example.Financial.Core.Finite public
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.Shortfall
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.FiniteShortfall using (positivePart-sum-bound)
open import Cubical.HITs.CauchyReals.Algebra.Order.Properties using (isIrrefl<ᵣ)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Bool.Base using (Bool; false; true)
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
import Cubical.Data.FinData.Base as F

-- Broker perspective: positive is a receipt, negative is a payment owed.
-- Coordinates are currencies, and quantities are in each currency's units.
Cashflow : ℕ → Type₀
Cashflow = Vector

incoming outgoing : ∀ {n} → Cashflow n → Cashflow n
incoming flow c = positivePart (flow c)
outgoing flow c = positivePart (-ᵣ flow c)

incoming-nonnegative : ∀ {n} (flow : Cashflow n) c → 0 ≤ᵣ incoming flow c
incoming-nonnegative flow c = positivePart-nonnegative (flow c)

outgoing-nonnegative : ∀ {n} (flow : Cashflow n) c → 0 ≤ᵣ outgoing flow c
outgoing-nonnegative flow c = positivePart-nonnegative (-ᵣ flow c)

incoming-minus-outgoing : ∀ {n} (flow : Cashflow n) c →
  incoming flow c -ᵣ outgoing flow c ≡ flow c
incoming-minus-outgoing flow c =
  cong (_-ᵣ outgoing flow c) (sym shifted) ∙ cancel
  where
  shifted : outgoing flow c +ᵣ flow c ≡ incoming flow c
  shifted = +ᵣMaxDistr (-ᵣ flow c) 0 (flow c)
    ∙ cong₂ maxᵣ (+ᵣComm (-ᵣ flow c) (flow c) ∙ +-ᵣ (flow c)) (+IdL (flow c))
    ∙ maxᵣComm 0 (flow c)
  cancel : (outgoing flow c +ᵣ flow c) -ᵣ outgoing flow c ≡ flow c
  cancel = ℝ!

-- A book groups trades at ONE settlement date. The date-indexed version
-- below deliberately never nets payments across different dates.
Book : ℕ → ℕ → Type₀
Book trades currencies = Fin trades → Cashflow currencies

netFlow : ∀ {trades currencies} → Book trades currencies → Cashflow currencies
netFlow book c = sum (λ trade → book trade c)

grossOutgoing netOutgoing : ∀ {trades currencies} → Book trades currencies → Cashflow currencies
grossOutgoing book c = sum (λ trade → outgoing (book trade) c)
netOutgoing book = outgoing (netFlow book)

netOutgoing≤grossOutgoing : ∀ {trades currencies} (book : Book trades currencies) c →
  netOutgoing book c ≤ᵣ grossOutgoing book c
netOutgoing≤grossOutgoing book c = isTrans≡≤ᵣ _ _ _
  (cong positivePart (sym (sum-negate (λ trade → book trade c))))
  (positivePart-sum-bound (λ trade → -ᵣ book trade c))

grossOutgoing-nonnegative : ∀ {trades currencies} (book : Book trades currencies) c →
  0 ≤ᵣ grossOutgoing book c
grossOutgoing-nonnegative book c = sum-nonnegative _
  (λ trade → outgoing-nonnegative (book trade) c)

DatedBook : ℕ → ℕ → ℕ → Type₀
DatedBook dates trades currencies = Fin dates → Book trades currencies

datedGrossOutgoing datedNetOutgoing : ∀ {dates trades currencies} →
  DatedBook dates trades currencies → Fin dates → Cashflow currencies
datedGrossOutgoing book date = grossOutgoing (book date)
datedNetOutgoing book date = netOutgoing (book date)

dated-net≤gross : ∀ {dates trades currencies} (book : DatedBook dates trades currencies) date c →
  datedNetOutgoing book date c ≤ᵣ datedGrossOutgoing book date c
dated-net≤gross book date = netOutgoing≤grossOutgoing (book date)

-- These are native-currency liquidity obligations. A base-currency mark
-- does not supply a payment balance in a different currency.
FundingCertificate : ∀ {n} → Cashflow n → Cashflow n → Type₀
FundingCertificate flow buffers = ∀ c → outgoing flow c ≤ᵣ buffers c

GrossFundingCertificate : ∀ {trades currencies} →
  Book trades currencies → Cashflow currencies → Type₀
GrossFundingCertificate book buffers = ∀ c → grossOutgoing book c ≤ᵣ buffers c

DatedFundingCertificate : ∀ {dates trades currencies} →
  DatedBook dates trades currencies → (Fin dates → Cashflow currencies) → Type₀
DatedFundingCertificate book buffers = ∀ date → GrossFundingCertificate (book date) (buffers date)

funding-isProp : ∀ {n} (flow buffers : Cashflow n) → isProp (FundingCertificate flow buffers)
funding-isProp flow buffers = isPropΠ (λ _ → isProp≤ᵣ _ _)

gross-funding-isProp : ∀ {trades currencies} (book : Book trades currencies) buffers →
  isProp (GrossFundingCertificate book buffers)
gross-funding-isProp book buffers = isPropΠ (λ _ → isProp≤ᵣ _ _)

-- Algebraic netting needs no more liquidity than the gross book. Whether
-- legal payment netting is available for a given group is separate input;
-- this inequality does not authorize replacing gross payment obligations.
gross-funding-covers-net : ∀ {trades currencies} (book : Book trades currencies) buffers →
  GrossFundingCertificate book buffers → FundingCertificate (netFlow book) buffers
gross-funding-covers-net book buffers covered c =
  isTrans≤ᵣ _ _ _ (netOutgoing≤grossOutgoing book c) (covered c)

funding-monotone : ∀ {n} (flow buffers larger : Cashflow n) →
  (∀ c → buffers c ≤ᵣ larger c) → FundingCertificate flow buffers → FundingCertificate flow larger
funding-monotone flow buffers larger grow covered c =
  isTrans≤ᵣ _ _ _ (covered c) (grow c)

-- FX factors are base-currency units per unit of each native currency.
-- They are a supplied conversion scenario, not a same-day funding facility.
baseMark : ∀ {n} → Vector n → Cashflow n → ℝ
baseMark fx flow = dot fx flow

principalAtRisk : ∀ {n} → Vector n → Cashflow n → ℝ
principalAtRisk fx flow = dot fx (outgoing flow)

principal-nonnegative : ∀ {n} (fx : Vector n) flow →
  (∀ c → 0 ≤ᵣ fx c) → 0 ≤ᵣ principalAtRisk fx flow
principal-nonnegative fx flow fx₊ = dot-nonnegative fx (outgoing flow) fx₊
  (outgoing-nonnegative flow)

funding-covers-principal : ∀ {n} (fx : Vector n) flow buffers →
  (∀ c → 0 ≤ᵣ fx c) → FundingCertificate flow buffers →
  principalAtRisk fx flow ≤ᵣ dot fx buffers
funding-covers-principal fx flow buffers fx₊ = dot-monotone fx (outgoing flow) buffers fx₊

net-principal≤gross : ∀ {trades currencies} (fx : Vector currencies)
  (book : Book trades currencies) → (∀ c → 0 ≤ᵣ fx c) →
  principalAtRisk fx (netFlow book) ≤ᵣ dot fx (grossOutgoing book)
net-principal≤gross fx book fx₊ = dot-monotone fx (netOutgoing book) (grossOutgoing book) fx₊
  (netOutgoing≤grossOutgoing book)

gross-principal-sum : ∀ {trades currencies} (fx : Vector currencies)
  (book : Book trades currencies) →
  dot fx (grossOutgoing book) ≡ sum (λ trade → principalAtRisk fx (book trade))
gross-principal-sum fx book =
  sum-cong _ _ (λ c → sym (sum-scale (fx c) (λ trade → outgoing (book trade) c)))
  ∙ sum-exchange (λ c trade → fx c ·ᵣ outgoing (book trade) c)

-- A deliberately small delivery model: all outgoing payments have either
-- been irrevocably released or not. Receipts are pending, final, or failed.
-- In the failed state, assume zero recovery of the released principal.
data ReceiptState : Type₀ where
  pending received failed : ReceiptState

record SettlementState : Type₀ where
  constructor settlement-state
  field
    released : Bool
    receipt : ReceiptState
open SettlementState public

settlementPrincipalExposure : ∀ {n} → Vector n → Cashflow n → SettlementState → ℝ
settlementPrincipalExposure fx flow (settlement-state false r) = 0
settlementPrincipalExposure fx flow (settlement-state true pending) = principalAtRisk fx flow
settlementPrincipalExposure fx flow (settlement-state true received) = 0
settlementPrincipalExposure fx flow (settlement-state true failed) = principalAtRisk fx flow

settlementPrincipalLoss : ∀ {n} → Vector n → Cashflow n → SettlementState → ℝ
settlementPrincipalLoss fx flow (settlement-state false r) = 0
settlementPrincipalLoss fx flow (settlement-state true pending) = 0
settlementPrincipalLoss fx flow (settlement-state true received) = 0
settlementPrincipalLoss fx flow (settlement-state true failed) = principalAtRisk fx flow

principal-exposure-bound : ∀ {n} (fx : Vector n) flow state → (∀ c → 0 ≤ᵣ fx c) →
  settlementPrincipalExposure fx flow state ≤ᵣ principalAtRisk fx flow
principal-exposure-bound fx flow (settlement-state false r) fx₊ = principal-nonnegative fx flow fx₊
principal-exposure-bound fx flow (settlement-state true pending) fx₊ = ≤ᵣ-refl _
principal-exposure-bound fx flow (settlement-state true received) fx₊ = principal-nonnegative fx flow fx₊
principal-exposure-bound fx flow (settlement-state true failed) fx₊ = ≤ᵣ-refl _

principal-loss≤exposure : ∀ {n} (fx : Vector n) flow state → (∀ c → 0 ≤ᵣ fx c) →
  settlementPrincipalLoss fx flow state ≤ᵣ settlementPrincipalExposure fx flow state
principal-loss≤exposure fx flow (settlement-state false r) fx₊ = ≤ᵣ-refl 0
principal-loss≤exposure fx flow (settlement-state true pending) fx₊ = principal-nonnegative fx flow fx₊
principal-loss≤exposure fx flow (settlement-state true received) fx₊ = ≤ᵣ-refl 0
principal-loss≤exposure fx flow (settlement-state true failed) fx₊ = ≤ᵣ-refl _

principal-loss-bound : ∀ {n} (fx : Vector n) flow state → (∀ c → 0 ≤ᵣ fx c) →
  settlementPrincipalLoss fx flow state ≤ᵣ principalAtRisk fx flow
principal-loss-bound fx flow state fx₊ = isTrans≤ᵣ _ _ _
  (principal-loss≤exposure fx flow state fx₊) (principal-exposure-bound fx flow state fx₊)

funding-covers-stage-loss : ∀ {n} (fx : Vector n) flow buffers state →
  (∀ c → 0 ≤ᵣ fx c) → FundingCertificate flow buffers →
  settlementPrincipalLoss fx flow state ≤ᵣ dot fx buffers
funding-covers-stage-loss fx flow buffers state fx₊ covered = isTrans≤ᵣ _ _ _
  (principal-loss-bound fx flow state fx₊) (funding-covers-principal fx flow buffers fx₊ covered)

-- An idealized payment-versus-payment guarantee is an INPUT protocol law:
-- released outgoing principal implies that the incoming leg is final too.
-- Only settlement principal exposure is covered, not replacement cost,
-- funding cost, market risk, or the failure of a real settlement protocol.
AtomicExchange : SettlementState → Type₀
AtomicExchange state = released state ≡ true → receipt state ≡ received

pvp-principal-exposure-zero : ∀ {n} (fx : Vector n) flow state → AtomicExchange state →
  settlementPrincipalExposure fx flow state ≡ 0
pvp-principal-exposure-zero fx flow (settlement-state false r) atomic = refl
pvp-principal-exposure-zero fx flow (settlement-state true r) atomic =
  subst (λ s → settlementPrincipalExposure fx flow (settlement-state true s) ≡ 0)
    (sym (atomic refl)) refl

pvp-principal-loss-zero : ∀ {n} (fx : Vector n) flow state → AtomicExchange state →
  settlementPrincipalLoss fx flow state ≡ 0
pvp-principal-loss-zero fx flow (settlement-state false r) atomic = refl
pvp-principal-loss-zero fx flow (settlement-state true r) atomic =
  subst (λ s → settlementPrincipalLoss fx flow (settlement-state true s) ≡ 0)
    (sym (atomic refl)) refl
