{-# OPTIONS --safe --cubical #-}

-- Currency-specific funding and gross versus net payment obligations follow
-- the distinctions in ../../REFERENCES.md#bcbs-settlement-2013.
-- The principal 100 and spot 1 are synthetic. A zero domestic mark is not
-- a liquidity certificate, and algebraic cancellation creates no legal
-- payment-netting right; ideal PvP only addresses the stated principal risk.

module Cubical.HITs.CauchyReals.Example.Financial.Examples.Settlement.TwoCurrencyExample where

open import Cubical.HITs.CauchyReals.Example.Financial.Core.Vectors public using (two)

open import Cubical.HITs.CauchyReals.Example.Financial.Settlement.Base
open import Cubical.HITs.CauchyReals.Example.Financial.Core.Finite public
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.Shortfall
open import Cubical.HITs.CauchyReals.Algebra.Order.Properties using (isIrrefl<ᵣ)
open import Cubical.Data.Empty using (⊥)
open import Cubical.Data.Bool.Base using (Bool; false; true)
open import Cubical.Tactics.CommRingSolver.Specialised.Reals
import Cubical.Data.FinData.Base as F

-- Coordinate zero is domestic; coordinate one is foreign.
swapFlow spot domesticBuffer foreignOnlyBuffer : Cashflow 2
swapFlow = two -100 100
spot = two 1 1
domesticBuffer = two 100 0
foreignOnlyBuffer = two 0 100

incoming-profile : incoming swapFlow ≡ two 0 100
incoming-profile = funExt λ
  { F.zero → positivePart-of-nonpositive -100 decℚ≤ᵣ?
  ; (F.suc F.zero) → positivePart-of-nonnegative 100 decℚ≤ᵣ?
  }

outgoing-profile : outgoing swapFlow ≡ two 100 0
outgoing-profile = funExt λ
  { F.zero → cong positivePart negate-negative ∙ positivePart-of-nonnegative 100 decℚ≤ᵣ?
  ; (F.suc F.zero) → cong positivePart negate-positive ∙ positivePart-of-nonpositive -100 decℚ≤ᵣ?
  }
  where
  negate-negative : -ᵣ (-100) ≡ 100
  negate-negative = ℝ!
  negate-positive : -ᵣ 100 ≡ -100
  negate-positive = ℝ!

zero-base-mark : baseMark spot swapFlow ≡ 0
zero-base-mark = ℝ!

domestic-funding-needed : outgoing swapFlow F.zero ≡ 100
domestic-funding-needed = funExt⁻ outgoing-profile F.zero

funded-in-required-currency : FundingCertificate swapFlow domesticBuffer
funded-in-required-currency c = ≡ᵣWeaken≤ᵣ _ _ (funExt⁻ outgoing-profile c)

-- Even holding 100 units of the foreign currency does not meet the
-- domestic payment obligation in this certificate, without an FX trade.
foreign-buffer-insufficient : FundingCertificate swapFlow foreignOnlyBuffer → ⊥
foreign-buffer-insufficient covered = isIrrefl<ᵣ 0
  (isTrans<≤ᵣ 0 100 0 decℚ<ᵣ?
    (isTrans≡≤ᵣ _ _ _ (sym domestic-funding-needed) (covered F.zero)))

principal-one-hundred : principalAtRisk spot swapFlow ≡ 100
principal-one-hundred = cong (dot spot) outgoing-profile ∙ ℝ!

paid-before-receipt-exposure :
  settlementPrincipalExposure spot swapFlow (settlement-state true pending) ≡ 100
paid-before-receipt-exposure = principal-one-hundred

failed-after-payment-loss :
  settlementPrincipalLoss spot swapFlow (settlement-state true failed) ≡ 100
failed-after-payment-loss = principal-one-hundred

atomic-completed-loss :
  settlementPrincipalLoss spot swapFlow (settlement-state true received) ≡ 0
atomic-completed-loss = pvp-principal-loss-zero spot swapFlow
  (settlement-state true received) (λ _ → refl)

-- Two reversing trades economically cancel at the same date. Their
-- original gross payment instructions still require both currencies.
reversalBook : Book 2 2
reversalBook F.zero = swapFlow
reversalBook (F.suc F.zero) c = -ᵣ swapFlow c

reversal-net-zero : netFlow reversalBook ≡ (λ _ → 0)
reversal-net-zero = funExt (λ c → ℝ!)

reversal-net-outgoing-zero : netOutgoing reversalBook ≡ (λ _ → 0)
reversal-net-outgoing-zero = cong outgoing reversal-net-zero
  ∙ funExt (λ c → cong positivePart negate-zero ∙ positivePart-zero)
  where
  negate-zero : -ᵣ 0 ≡ 0
  negate-zero = ℝ!

reversal-gross-profile : grossOutgoing reversalBook ≡ two 100 100
reversal-gross-profile = funExt λ c →
  cong (outgoing swapFlow c +ᵣ_)
    (cong (_+ᵣ 0) (cong positivePart (-ᵣInvol (swapFlow c)))
      ∙ +IdR (incoming swapFlow c))
  ∙ cong₂ _+ᵣ_ (funExt⁻ outgoing-profile c) (funExt⁻ incoming-profile c)
  ∙ combine c
  where
  combine : ∀ c → two 100 0 c +ᵣ two 0 100 c ≡ two 100 100 c
  combine F.zero = ℝ!
  combine (F.suc F.zero) = ℝ!

reversal-gross-base-two-hundred : dot spot (grossOutgoing reversalBook) ≡ 200
reversal-gross-base-two-hundred = cong (dot spot) reversal-gross-profile ∙ ℝ!

reversal-net-funded-at-zero : FundingCertificate (netFlow reversalBook) (λ _ → 0)
reversal-net-funded-at-zero c = ≡ᵣWeaken≤ᵣ _ _ (funExt⁻ reversal-net-outgoing-zero c)

reversal-gross-needs-funding : GrossFundingCertificate reversalBook (λ _ → 0) → ⊥
reversal-gross-needs-funding covered = isIrrefl<ᵣ 0
  (isTrans<≤ᵣ 0 100 0 decℚ<ᵣ?
    (isTrans≡≤ᵣ _ _ _ (sym (funExt⁻ reversal-gross-profile F.zero)) (covered F.zero)))
