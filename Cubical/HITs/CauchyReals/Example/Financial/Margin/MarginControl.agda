module Cubical.HITs.CauchyReals.Example.Financial.Margin.MarginControl where

open import Cubical.HITs.CauchyReals.Example.Financial.Margin.Base public
open import Cubical.HITs.CauchyReals.Example.Financial.Risk.Shortfall
open import Cubical.HITs.CauchyReals.Foundation.Rationals using (ℚ; module ℚ; fromNatℚ)
open import Cubical.Relation.Nullary using (yes; no; ¬_)
open import Cubical.Tactics.CommRingSolver.Specialised.Reals

-- An exact rational call amount comes with equality to the scenario model.
-- This interface does not assume that arbitrary Cauchy-real calls are rational.
record ExactMargin {n : ℕ} (X C : Vector (suc n)) : Type₀ where
  field
    amount : ℚ
    exact : requiredMargin X C ≡ rat amount
open ExactMargin public

amount-nonnegative : ∀ {n} {X C : Vector (suc n)} (report : ExactMargin X C) →
  0 ℚ.≤ amount report
amount-nonnegative {X = X} {C = C} report = ≤ᵣ→≤ℚ 0 (amount report)
  (isTrans≤≡ᵣ _ _ _ (requiredMargin-nonnegative X C) (exact report))

-- The requested further cash is nonnegative, including after overpayment.
-- Payment means received, available, domestic collateral credited at par.
outstandingRequest : ∀ {n} {X C : Vector (suc n)} → ExactMargin X C → ℚ → ℚ
outstandingRequest report paid = ℚ.max (amount report ℚ.- paid) 0

request-nonnegative : ∀ {n} {X C : Vector (suc n)} (report : ExactMargin X C) paid →
  0 ℚ.≤ outstandingRequest report paid
request-nonnegative report paid = ℚ.≤max' (amount report ℚ.- paid) 0

private
  request-positivePart : ∀ {n} {X C : Vector (suc n)} (report : ExactMargin X C) paid →
    rat (outstandingRequest report paid) ≡ positivePart (rat (amount report) -ᵣ rat paid)
  request-positivePart report paid = sym (stopLoss-rat (amount report) paid)

-- This is a required TOTAL payment, not evidence that the new request has
-- been met. Only postCash below changes the collateral state in the model.
request-covers : ∀ {n} {X C : Vector (suc n)} (report : ExactMargin X C) paid →
  requiredMargin X C ≤ᵣ rat paid +ᵣ rat (outstandingRequest report paid)
request-covers report paid = isTrans≡≤ᵣ _ _ _ (exact report)
  (isTrans≤≡ᵣ _ _ _ (stopLoss-reconstruct (rat (amount report)) (rat paid))
    (cong (rat paid +ᵣ_) (sym (request-positivePart report paid))))

request-minimal : ∀ {n} {X C : Vector (suc n)} (report : ExactMargin X C) paid further →
  0 ≤ᵣ further → requiredMargin X C ≤ᵣ rat paid +ᵣ further →
  rat (outstandingRequest report paid) ≤ᵣ further
request-minimal report paid further further₊ sufficient =
  isTrans≡≤ᵣ _ _ _ (request-positivePart report paid)
    (stopLoss-upper (rat (amount report)) (rat paid) further further₊
      (subst (_≤ᵣ (rat paid +ᵣ further)) (exact report) sufficient))

request-paid-zero : ∀ {n} {X C : Vector (suc n)} (report : ExactMargin X C) paid →
  requiredMargin X (postCash (postCash C (rat paid)) (rat (outstandingRequest report paid))) ≡ 0
request-paid-zero {X = X} {C = C} report paid =
  cong (requiredMargin X)
    (funExt (λ i → sym (+ᵣAssoc (C i) (rat paid) (rat (outstandingRequest report paid)))))
  ∙ sufficient-cash-zero X C (rat paid +ᵣ rat (outstandingRequest report paid))
      (request-covers report paid)

-- With a nonnegative actual payment, the outstanding request equals the
-- margin recomputed on the remaining exposure. This is stronger than merely
-- finding a sufficient further amount. A negative payment is a withdrawal
-- and is intentionally excluded from this equality theorem.
outstanding-exact : ∀ {n} {X C : Vector (suc n)} (report : ExactMargin X C) paid →
  0 ℚ.≤ paid → requiredMargin X (postCash C (rat paid)) ≡ rat (outstandingRequest report paid)
outstanding-exact {X = X} {C = C} report paid paid₊ =
  margin-postCash X C (rat paid) (≤ℚ→≤ᵣ 0 paid paid₊)
  ∙ cong (λ m → stopLoss m (rat paid)) (exact report)
  ∙ stopLoss-rat (amount report) paid

-- Updating a report records the additional cash actually received. Its new
-- amount can be used directly by the same payment and request operations.
recordPayment : ∀ {n} {X C : Vector (suc n)} (report : ExactMargin X C) paid →
  0 ℚ.≤ paid → ExactMargin X (postCash C (rat paid))
recordPayment report paid paid₊ .amount = outstandingRequest report paid
recordPayment report paid paid₊ .exact = outstanding-exact report paid paid₊

data PaymentStatus : Type₀ where
  covered more-due : PaymentStatus

data PaymentVerdict {n : ℕ} (X C : Vector (suc n)) (paid : ℚ) : Type₀ where
  fully-covered : (∀ i → X i ≤ᵣ C i +ᵣ rat paid) →
    requiredMargin X (postCash C (rat paid)) ≡ 0 → PaymentVerdict X C paid
  insufficient : ¬ (requiredMargin X C ≤ᵣ rat paid) → PaymentVerdict X C paid

payment-status : ∀ {n} {X C : Vector (suc n)} {paid} → PaymentVerdict X C paid → PaymentStatus
payment-status (fully-covered _ _) = covered
payment-status (insufficient _) = more-due

-- This decision compares only certified rational amounts. There is no
-- branch on the order, equality, or sign of an arbitrary Cauchy real.
checkPayment : ∀ {n} {X C : Vector (suc n)} (report : ExactMargin X C) paid →
  0 ℚ.≤ paid → PaymentVerdict X C paid
checkPayment {X = X} {C = C} report paid paid₊ with ℚ.≤Dec (amount report) paid
... | yes amount≤paid = fully-covered (margin-bound→coverage X C (rat paid) sufficient)
  (sufficient-cash-zero X C (rat paid) sufficient)
  where
  sufficient : requiredMargin X C ≤ᵣ rat paid
  sufficient = isTrans≡≤ᵣ _ _ _ (exact report) (≤ℚ→≤ᵣ _ _ amount≤paid)
... | no amount≰paid = insufficient λ sufficient → amount≰paid
  (≤ᵣ→≤ℚ (amount report) paid
    (subst (_≤ᵣ rat paid) (exact report) sufficient))

-- An insufficient nonnegative payment leaves a nonzero residual call.
insufficient-residual-nonzero : ∀ {n} {X C : Vector (suc n)} paid → 0 ℚ.≤ paid →
  ¬ (requiredMargin X C ≤ᵣ rat paid) → ¬ (requiredMargin X (postCash C (rat paid)) ≡ 0)
insufficient-residual-nonzero {X = X} {C = C} paid paid₊ not-covered zero-residual = not-covered
  (margin-least X C (rat paid) (≤ℚ→≤ᵣ 0 paid paid₊) λ i →
    isTrans≤≡ᵣ _ _ _ (margin-coverage X (postCash C (rat paid)) i)
      (cong (postCash C (rat paid) i +ᵣ_) zero-residual ∙ +IdR (postCash C (rat paid) i)))
