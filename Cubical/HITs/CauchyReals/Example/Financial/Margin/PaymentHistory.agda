{-# OPTIONS --safe --cubical #-}

module Cubical.HITs.CauchyReals.Example.Financial.Margin.PaymentHistory where

open import Cubical.HITs.CauchyReals.Example.Financial.Margin.MarginControl
open import Cubical.HITs.CauchyReals.Foundation.Rationals using (ℚ; module ℚ; fromNatℚ)
open import Cubical.Data.List.Base using (List; []; _∷_; _++_)
open import Cubical.Data.Empty using (⊥; rec)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Foundations.Equiv using (_≃_; propBiimpl→Equiv)
open import Cubical.Foundations.Univalence using (ua)

-- A receipt represents actual additional domestic cash, eligible at par and
-- still available in every scenario. The claim and collateral valuation model
-- remain fixed throughout a history. There are no withdrawals or event IDs:
-- recording a receipt twice credits it twice, not an idempotent replay.
record Receipt : Type₀ where
  constructor receipt
  field
    received : ℚ
    received-nonnegative : 0 ℚ.≤ received
open Receipt public

PaymentHistory : Type₀
PaymentHistory = List Receipt

totalReceived : PaymentHistory → ℚ
totalReceived [] = 0
totalReceived (payment ∷ history) = received payment ℚ.+ totalReceived history

totalReceived-nonnegative : ∀ history → 0 ℚ.≤ totalReceived history
totalReceived-nonnegative [] = ℚ.isRefl≤ 0
totalReceived-nonnegative (payment ∷ history) =
  subst (λ q → q ℚ.≤ totalReceived (payment ∷ history)) (ℚ.+IdL 0)
    (ℚ.≤Monotone+ 0 (received payment) 0 (totalReceived history)
      (received-nonnegative payment) (totalReceived-nonnegative history))

-- Cash is credited in list order over an arbitrary scenario domain, retaining
-- the full collateral state even after the outstanding call has reached zero.
-- Finite postCash is the definitional specialization used by report updates.
creditHistory : ∀ {ℓ} {S : Type ℓ} → (S → ℝ) → PaymentHistory → S → ℝ
creditHistory C [] = C
creditHistory C (payment ∷ history) =
  creditHistory (λ state → C state +ᵣ rat (received payment)) history

processHistory : ∀ {n} {X C : Vector (suc n)} →
  ExactMargin X C → (history : PaymentHistory) → ExactMargin X (creditHistory C history)
processHistory report [] = report
processHistory report (payment ∷ history) = processHistory
  (recordPayment report (received payment) (received-nonnegative payment)) history

-- The key accounting invariant holds for every finite history, including
-- the empty history and histories that overpay the initial required margin.
creditHistory-total : ∀ {ℓ} {S : Type ℓ} (C : S → ℝ) history →
  creditHistory C history ≡ (λ state → C state +ᵣ rat (totalReceived history))
creditHistory-total C [] = funExt (λ i → sym (+IdR (C i)))
creditHistory-total C (payment ∷ history) =
  creditHistory-total (λ state → C state +ᵣ rat (received payment)) history
  ∙ funExt (λ i → sym (+ᵣAssoc (C i) (rat (received payment)) (rat (totalReceived history)))
      ∙ cong (C i +ᵣ_) (+ᵣ-rat (received payment) (totalReceived history)))

private
  rat-path-injective : ∀ p q → rat p ≡ rat q → p ≡ q
  rat-path-injective p q path = ℚ.isAntisym≤ p q
    (≤ᵣ→≤ℚ p q (≡ᵣWeaken≤ᵣ _ _ path))
    (≤ᵣ→≤ℚ q p (≡ᵣWeaken≤ᵣ _ _ (sym path)))

-- Equality of the rational report amounts follows from equality of their
-- real meanings. No canonical numerator/denominator representation is needed.
processHistory-outstanding : ∀ {n} {X C : Vector (suc n)}
  (report : ExactMargin X C) history →
  amount (processHistory report history) ≡ outstandingRequest report (totalReceived history)
processHistory-outstanding {X = X} {C = C} report history = rat-path-injective _ _
  (sym (exact (processHistory report history))
    ∙ cong (requiredMargin X) (creditHistory-total C history)
    ∙ outstanding-exact report (totalReceived history) (totalReceived-nonnegative history))

-- Exact reports for a fixed collateral state are propositions: the amount
-- is uniquely fixed by its meaning, and the real equality proof is irrelevant.
exactMargin-isProp : ∀ {n} (X C : Vector (suc n)) → isProp (ExactMargin X C)
exactMargin-isProp X C left right i .amount = amount-path i
  where
  amount-path : amount left ≡ amount right
  amount-path = rat-path-injective _ _ (sym (exact left) ∙ exact right)
exactMargin-isProp X C left right i .exact =
  isProp→PathP (λ j → isSetℝ (requiredMargin X C)
    (rat (rat-path-injective _ _ (sym (exact left) ∙ exact right) j)))
    (exact left) (exact right) i

-- Transport along the full collateral-state path identifies the entire
-- sequential report, including its exactness proof, with one batched payment.
processHistory-batch : ∀ {n} {X C : Vector (suc n)}
  (report : ExactMargin X C) history →
  subst (ExactMargin X) (creditHistory-total C history) (processHistory report history)
    ≡ recordPayment report (totalReceived history) (totalReceived-nonnegative history)
processHistory-batch {X = X} {C = C} report history =
  exactMargin-isProp X (postCash C (rat (totalReceived history))) _ _

totalReceived-append : ∀ first second →
  totalReceived (first ++ second) ≡ totalReceived first ℚ.+ totalReceived second
totalReceived-append [] second = sym (ℚ.+IdL (totalReceived second))
totalReceived-append (payment ∷ first) second =
  cong (received payment ℚ.+_) (totalReceived-append first second)
  ∙ ℚ.+Assoc (received payment) (totalReceived first) (totalReceived second)

creditHistory-append : ∀ {ℓ} {S : Type ℓ} (C : S → ℝ) first second →
  creditHistory C (first ++ second) ≡ creditHistory (creditHistory C first) second
creditHistory-append C [] second = refl
creditHistory-append C (payment ∷ first) second =
  creditHistory-append (λ state → C state +ᵣ rat (received payment)) first second

processHistory-append : ∀ {n} {X C : Vector (suc n)}
  (report : ExactMargin X C) first second →
  subst (ExactMargin X) (creditHistory-append C first second)
    (processHistory report (first ++ second))
  ≡ processHistory (processHistory report first) second
processHistory-append {X = X} {C = C} report first second =
  exactMargin-isProp X (creditHistory (creditHistory C first) second) _ _

-- Any two histories with equal totals yield the same collateral and report.
-- This covers batching and reordering without identifying unequal payments
-- or asserting that duplicate events can safely be discarded.
creditHistory-same-total : ∀ {ℓ} {S : Type ℓ} (C : S → ℝ) first second →
  totalReceived first ≡ totalReceived second → creditHistory C first ≡ creditHistory C second
creditHistory-same-total C first second totals = creditHistory-total C first
  ∙ cong (λ q state → C state +ᵣ rat q) totals ∙ sym (creditHistory-total C second)

processHistory-same-total-amount : ∀ {n} {X C : Vector (suc n)}
  (report : ExactMargin X C) first second → totalReceived first ≡ totalReceived second →
  amount (processHistory report first) ≡ amount (processHistory report second)
processHistory-same-total-amount report first second totals =
  processHistory-outstanding report first
  ∙ cong (outstandingRequest report) totals
  ∙ sym (processHistory-outstanding report second)

processHistory-same-total : ∀ {n} {X C : Vector (suc n)}
  (report : ExactMargin X C) first second (totals : totalReceived first ≡ totalReceived second) →
  subst (ExactMargin X) (creditHistory-same-total C first second totals)
    (processHistory report first) ≡ processHistory report second
processHistory-same-total {X = X} {C = C} report first second totals =
  exactMargin-isProp X (creditHistory C second) _ _

-- Exchanging any two finite batches preserves total receipts.
totalReceived-swap-batches : ∀ first second →
  totalReceived (first ++ second) ≡ totalReceived (second ++ first)
totalReceived-swap-batches first second = totalReceived-append first second
  ∙ ℚ.+Comm (totalReceived first) (totalReceived second)
  ∙ sym (totalReceived-append second first)

processHistory-swap-batches : ∀ {n} {X C : Vector (suc n)}
  (report : ExactMargin X C) first second →
  amount (processHistory report (first ++ second))
    ≡ amount (processHistory report (second ++ first))
processHistory-swap-batches report first second =
  processHistory-same-total-amount report (first ++ second) (second ++ first)
    (totalReceived-swap-batches first second)

HistoryCoverage : ∀ {n} → Vector (suc n) → Vector (suc n) → PaymentHistory → Type₀
HistoryCoverage X C history = ∀ i → X i ≤ᵣ creditHistory C history i

history-enough→coverage : ∀ {n} (X C : Vector (suc n)) history →
  requiredMargin X C ≤ᵣ rat (totalReceived history) → HistoryCoverage X C history
history-enough→coverage X C history sufficient i =
  subst (X i ≤ᵣ_) (sym (funExt⁻ (creditHistory-total C history) i))
    (margin-bound→coverage X C (rat (totalReceived history)) sufficient i)

history-coverage→enough : ∀ {n} (X C : Vector (suc n)) history →
  HistoryCoverage X C history → requiredMargin X C ≤ᵣ rat (totalReceived history)
history-coverage→enough X C history coverage =
  margin-least X C (rat (totalReceived history))
    (≤ℚ→≤ᵣ 0 _ (totalReceived-nonnegative history))
    (λ i → subst (X i ≤ᵣ_) (funExt⁻ (creditHistory-total C history) i) (coverage i))

history-coverage≃enough : ∀ {n} (X C : Vector (suc n)) history →
  HistoryCoverage X C history ≃ (requiredMargin X C ≤ᵣ rat (totalReceived history))
history-coverage≃enough X C history = propBiimpl→Equiv
  (isPropΠ (λ i → isProp≤ᵣ _ _)) (isProp≤ᵣ _ _)
  (history-coverage→enough X C history) (history-enough→coverage X C history)

history-coverage-path : ∀ {n} (X C : Vector (suc n)) history →
  HistoryCoverage X C history ≡ (requiredMargin X C ≤ᵣ rat (totalReceived history))
history-coverage-path X C history = ua (history-coverage≃enough X C history)

history-enough-zero : ∀ {n} (X C : Vector (suc n)) history →
  requiredMargin X C ≤ᵣ rat (totalReceived history) →
  requiredMargin X (creditHistory C history) ≡ 0
history-enough-zero X C history sufficient =
  margin-covered-zero X (creditHistory C history)
    (history-enough→coverage X C history sufficient)

history-zero→enough : ∀ {n} (X C : Vector (suc n)) history →
  requiredMargin X (creditHistory C history) ≡ 0 →
  requiredMargin X C ≤ᵣ rat (totalReceived history)
history-zero→enough X C history residual-zero =
  history-coverage→enough X C history λ i → isTrans≤≡ᵣ _ _ _
    (margin-coverage X (creditHistory C history) i)
    (cong (creditHistory C history i +ᵣ_) residual-zero
      ∙ +IdR (creditHistory C history i))

history-zero≃enough : ∀ {n} (X C : Vector (suc n)) history →
  (requiredMargin X (creditHistory C history) ≡ 0)
    ≃ (requiredMargin X C ≤ᵣ rat (totalReceived history))
history-zero≃enough X C history = propBiimpl→Equiv
  (isSetℝ _ _) (isProp≤ᵣ _ _)
  (history-zero→enough X C history) (history-enough-zero X C history)

processHistory-enough-zero : ∀ {n} {X C : Vector (suc n)}
  (report : ExactMargin X C) history → requiredMargin X C ≤ᵣ rat (totalReceived history) →
  amount (processHistory report history) ≡ 0
processHistory-enough-zero {X = X} {C = C} report history sufficient =
  rat-path-injective _ _
    (sym (exact (processHistory report history)) ∙ history-enough-zero X C history sufficient)

history-insufficient-nonzero : ∀ {n} (X C : Vector (suc n)) history →
  ¬ (requiredMargin X C ≤ᵣ rat (totalReceived history)) →
  ¬ (requiredMargin X (creditHistory C history) ≡ 0)
history-insufficient-nonzero X C history not-enough zero-margin =
  not-enough (history-zero→enough X C history zero-margin)

-- The decision uses only the original certified rational call and the sum
-- of actual receipts. Its covered branch still contains scenario coverage.
checkHistory : ∀ {n} {X C : Vector (suc n)} (report : ExactMargin X C) history →
  PaymentVerdict X C (totalReceived history)
checkHistory report history = checkPayment report (totalReceived history)
  (totalReceived-nonnegative history)

checkHistory-enough : ∀ {n} {X C : Vector (suc n)}
  (report : ExactMargin X C) history → requiredMargin X C ≤ᵣ rat (totalReceived history) →
  payment-status (checkHistory report history) ≡ covered
checkHistory-enough report history sufficient with checkHistory report history
... | fully-covered coverage residual-zero = refl
... | insufficient not-enough = rec (not-enough sufficient)

checkHistory-insufficient : ∀ {n} {X C : Vector (suc n)}
  (report : ExactMargin X C) history → ¬ (requiredMargin X C ≤ᵣ rat (totalReceived history)) →
  payment-status (checkHistory report history) ≡ more-due
checkHistory-insufficient {X = X} {C = C} report history not-enough
  with checkHistory report history
... | fully-covered coverage residual-zero = rec (not-enough
  (margin-least X C (rat (totalReceived history))
    (≤ℚ→≤ᵣ 0 _ (totalReceived-nonnegative history)) coverage))
... | insufficient insufficient-proof = refl

private
  covered-tag : PaymentStatus → Type₀
  covered-tag covered = Unit
  covered-tag more-due = ⊥

  more-due-not-covered : ¬ (more-due ≡ covered)
  more-due-not-covered path = subst covered-tag (sym path) tt

checkHistory-covered→enough : ∀ {n} {X C : Vector (suc n)}
  (report : ExactMargin X C) history → payment-status (checkHistory report history) ≡ covered →
  requiredMargin X C ≤ᵣ rat (totalReceived history)
checkHistory-covered→enough {X = X} {C = C} report history
  with checkHistory report history
... | fully-covered coverage residual-zero = λ _ →
  margin-least X C (rat (totalReceived history))
    (≤ℚ→≤ᵣ 0 _ (totalReceived-nonnegative history)) coverage
... | insufficient not-enough = λ path → rec (more-due-not-covered path)

checkHistory-no-false-covered : ∀ {n} {X C : Vector (suc n)}
  (report : ExactMargin X C) history → ¬ (requiredMargin X C ≤ᵣ rat (totalReceived history)) →
  ¬ (payment-status (checkHistory report history) ≡ covered)
checkHistory-no-false-covered report history not-enough path =
  not-enough (checkHistory-covered→enough report history path)

checkHistory-covered→coverage : ∀ {n} {X C : Vector (suc n)}
  (report : ExactMargin X C) history → payment-status (checkHistory report history) ≡ covered →
  HistoryCoverage X C history
checkHistory-covered→coverage {X = X} {C = C} report history status =
  history-enough→coverage X C history (checkHistory-covered→enough report history status)

receipt-path : (left right : Receipt) → received left ≡ received right → left ≡ right
receipt-path left right amounts i .received = amounts i
receipt-path left right amounts i .received-nonnegative =
  isProp→PathP (λ j → ℚ.isProp≤ 0 (amounts j))
    (received-nonnegative left) (received-nonnegative right) i

checkHistory-same-total : ∀ {n} {X C : Vector (suc n)}
  (report : ExactMargin X C) first second → totalReceived first ≡ totalReceived second →
  payment-status (checkHistory report first) ≡ payment-status (checkHistory report second)
checkHistory-same-total report first second totals =
  cong (λ payment → payment-status
    (checkPayment report (received payment) (received-nonnegative payment)))
    (receipt-path (receipt (totalReceived first) (totalReceived-nonnegative first))
      (receipt (totalReceived second) (totalReceived-nonnegative second)) totals)

-- Histories are assigned per client, so different clients may have different
-- numbers of receipts. No receipt or collateral surplus is pooled across them.
creditClientHistories : ∀ {clients n} → (Fin clients → Vector n) →
  (Fin clients → PaymentHistory) → Fin clients → Vector n
creditClientHistories collateral histories client =
  creditHistory (collateral client) (histories client)

creditClientHistories-total : ∀ {clients n} (collateral : Fin clients → Vector n) histories →
  creditClientHistories collateral histories
    ≡ (λ client → postCash (collateral client) (rat (totalReceived (histories client))))
creditClientHistories-total collateral histories =
  funExt (λ client → creditHistory-total (collateral client) (histories client))

processClientHistories : ∀ {clients n} {claims collateral : Fin clients → Vector (suc n)} →
  ((client : Fin clients) → ExactMargin (claims client) (collateral client)) →
  (histories : Fin clients → PaymentHistory) → (client : Fin clients) →
  ExactMargin (claims client) (creditClientHistories collateral histories client)
processClientHistories reports histories client = processHistory (reports client) (histories client)

processClientHistories-outstanding : ∀ {clients n}
  {claims collateral : Fin clients → Vector (suc n)}
  (reports : (client : Fin clients) → ExactMargin (claims client) (collateral client)) histories →
  (λ client → amount (processClientHistories reports histories client))
    ≡ (λ client → outstandingRequest (reports client) (totalReceived (histories client)))
processClientHistories-outstanding reports histories =
  funExt (λ client → processHistory-outstanding (reports client) (histories client))
