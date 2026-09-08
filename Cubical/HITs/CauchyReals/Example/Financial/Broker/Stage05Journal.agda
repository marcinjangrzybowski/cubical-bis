{-# OPTIONS --safe --cubical #-}

-- Identified business events and application-level duplicate suppression:
-- REFERENCES.md#cdm-event-model and REFERENCES.md#saltzer-1984.
-- The immutable catalog supplies actual received, eligible domestic cash.
-- This stage proves pure accounting laws, not authentication, durable storage,
-- network exactly-once delivery, or admission of changed payloads under an ID.

module Cubical.HITs.CauchyReals.Example.Financial.Broker.Stage05Journal where

open import Cubical.HITs.CauchyReals.Example.Financial.Core.Finite
open import Cubical.HITs.CauchyReals.Foundation.Rationals using (ℚ; module ℚ; fromNatℚ; ℚ!)
open import Cubical.Data.Bool using
  (Bool; true; false; _or_; _and_; not; if_then_else_; Dec→Bool;
   or-assoc; or-comm; or-idem; or-zeroʳ; false≢true)
open import Cubical.Data.List.Base using (List; []; _∷_; _++_)
open import Cubical.Data.FinData.Properties using (discreteFin)
open import Cubical.Relation.Nullary using (yes; no; ¬_)
import Cubical.Data.FinData.Base as F
import Cubical.Data.Empty as Empty

-- Event IDs are stable across replay. Ownership and amount are selected by
-- ID from this fixed catalog; ingest has no payload-replacement parameter.
-- Catalog construction and receipt provenance are supplied external inputs.
record EventCatalog (events clients : ℕ) : Type₀ where
  constructor event-catalog
  field
    owner : Fin events → Fin clients
    eventAmount : Fin events → ℚ
    eventAmount-nonnegative : ∀ event → 0 ℚ.≤ eventAmount event
open EventCatalog public

private
  sumℚ : ∀ {n} → (Fin n → ℚ) → ℚ
  sumℚ {zero} values = 0
  sumℚ {suc n} values = values F.zero ℚ.+ sumℚ (λ i → values (F.suc i))

  sumℚ-cong : ∀ {n} (left right : Fin n → ℚ) →
    (∀ i → left i ≡ right i) → sumℚ left ≡ sumℚ right
  sumℚ-cong left right paths = cong sumℚ (funExt paths)

  sumℚ-zero : ∀ n → sumℚ {n} (λ _ → 0) ≡ 0
  sumℚ-zero zero = refl
  sumℚ-zero (suc n) = cong (0 ℚ.+_) (sumℚ-zero n) ∙ ℚ.+IdL 0

  sumℚ-add : ∀ {n} (left right : Fin n → ℚ) →
    sumℚ (λ i → left i ℚ.+ right i) ≡ sumℚ left ℚ.+ sumℚ right
  sumℚ-add {zero} left right = sym (ℚ.+IdL 0)
  sumℚ-add {suc n} left right =
    cong ((left F.zero ℚ.+ right F.zero) ℚ.+_)
      (sumℚ-add (λ i → left (F.suc i)) (λ i → right (F.suc i)))
    ∙ shuffle (left F.zero) (right F.zero)
      (sumℚ (λ i → left (F.suc i))) (sumℚ (λ i → right (F.suc i)))
    where
    shuffle : ∀ a b c d → (a ℚ.+ b) ℚ.+ (c ℚ.+ d) ≡ (a ℚ.+ c) ℚ.+ (b ℚ.+ d)
    shuffle a b c d = ℚ!

  sumℚ-monotone : ∀ {n} (left right : Fin n → ℚ) →
    (∀ i → left i ℚ.≤ right i) → sumℚ left ℚ.≤ sumℚ right
  sumℚ-monotone {zero} left right bounds = ℚ.isRefl≤ 0
  sumℚ-monotone {suc n} left right bounds = ℚ.≤Monotone+ _ _ _ _ (bounds F.zero)
    (sumℚ-monotone (λ i → left (F.suc i)) (λ i → right (F.suc i))
      (λ i → bounds (F.suc i)))

  sumℚ-nonnegative : ∀ {n} (values : Fin n → ℚ) →
    (∀ i → 0 ℚ.≤ values i) → 0 ℚ.≤ sumℚ values
  sumℚ-nonnegative {n} values positive =
    subst (ℚ._≤ sumℚ values) (sumℚ-zero n)
      (sumℚ-monotone (λ _ → 0) values positive)

  rat-sumℚ : ∀ {n} (values : Fin n → ℚ) → rat (sumℚ values) ≡ sum (λ i → rat (values i))
  rat-sumℚ {zero} values = refl
  rat-sumℚ {suc n} values = sym (+ᵣ-rat _ _)
    ∙ cong (rat (values F.zero) +ᵣ_) (rat-sumℚ (λ i → values (F.suc i)))

  credited : Bool → ℚ → ℚ
  credited false value = 0
  credited true value = value

  credited-zero : ∀ seen → credited seen 0 ≡ 0
  credited-zero false = refl
  credited-zero true = refl

  credited-nonnegative : ∀ seen value → 0 ℚ.≤ value → 0 ℚ.≤ credited seen value
  credited-nonnegative false value positive = ℚ.isRefl≤ 0
  credited-nonnegative true value positive = positive

  credited-monotone : ∀ before after value → 0 ℚ.≤ value →
    (before ≡ true → after ≡ true) → credited before value ℚ.≤ credited after value
  credited-monotone false false value positive extension = ℚ.isRefl≤ 0
  credited-monotone false true value positive extension = positive
  credited-monotone true false value positive extension = Empty.rec (false≢true (extension refl))
  credited-monotone true true value positive extension = ℚ.isRefl≤ value

  or-swap : ∀ a b c → a or (b or c) ≡ b or (a or c)
  or-swap a b c = or-assoc a b c ∙ cong (_or c) (or-comm a b) ∙ sym (or-assoc b a c)

  or-repeat : ∀ a b → a or (a or b) ≡ a or b
  or-repeat a b = or-assoc a a b ∙ cong (_or b) (or-idem a)

  -- A previously seen event contributes no further cash; a new event adds
  -- its amount once. This equation also covers zero-valued receipts.
  credited-union : ∀ previous incoming value →
    credited (incoming or previous) value
      ≡ credited previous value ℚ.+ credited (incoming and not previous) value
  credited-union false false value = sym (ℚ.+IdL 0)
  credited-union false true value = sym (ℚ.+IdL value)
  credited-union true false value = sym (ℚ.+IdR value)
  credited-union true true value = sym (ℚ.+IdR value)

module Journal {events clients : ℕ} (catalog : EventCatalog events clients) where

  Ledger : Type₀
  Ledger = Fin events → Bool

  Batch : Type₀
  Batch = List (Fin events)

  emptyLedger : Ledger
  emptyLedger _ = false

  eventMask : Fin events → Ledger
  eventMask event query = Dec→Bool (discreteFin event query)

  eventMask-hit : ∀ event → eventMask event event ≡ true
  eventMask-hit event with discreteFin event event
  ... | yes equality = refl
  ... | no distinct = Empty.rec (distinct refl)

  eventMask-miss : ∀ event query → ¬ (event ≡ query) → eventMask event query ≡ false
  eventMask-miss event query distinct with discreteFin event query
  ... | yes equality = Empty.rec (distinct equality)
  ... | no different = refl

  ingest : Ledger → Fin events → Ledger
  ingest ledger event query = eventMask event query or ledger query

  ingest-hit : ∀ ledger event → ingest ledger event event ≡ true
  ingest-hit ledger event = cong (_or ledger event) (eventMask-hit event)

  ingest-miss : ∀ ledger event query → ¬ (event ≡ query) →
    ingest ledger event query ≡ ledger query
  ingest-miss ledger event query distinct = cong (_or ledger query) (eventMask-miss event query distinct)

  ingest-idempotent : ∀ ledger event → ingest (ingest ledger event) event ≡ ingest ledger event
  ingest-idempotent ledger event = funExt (λ query → or-repeat (eventMask event query) (ledger query))

  -- Commutation holds even when the two supplied IDs are equal.
  ingest-commutes : ∀ ledger first second →
    ingest (ingest ledger first) second ≡ ingest (ingest ledger second) first
  ingest-commutes ledger first second =
    funExt (λ query → or-swap (eventMask second query) (eventMask first query) (ledger query))

  SeenIn : Ledger → Ledger → Type₀
  SeenIn before after = ∀ event → before event ≡ true → after event ≡ true

  ingest-preserves-seen : ∀ ledger event → SeenIn ledger (ingest ledger event)
  ingest-preserves-seen ledger event query seen =
    cong (eventMask event query or_) seen ∙ or-zeroʳ (eventMask event query)

  attributedAmount : Fin events → Fin clients → ℚ
  attributedAmount event client with discreteFin (owner catalog event) client
  ... | yes equality = eventAmount catalog event
  ... | no distinct = 0

  attributedAmount-nonnegative : ∀ event client → 0 ℚ.≤ attributedAmount event client
  attributedAmount-nonnegative event client with discreteFin (owner catalog event) client
  ... | yes equality = eventAmount-nonnegative catalog event
  ... | no distinct = ℚ.isRefl≤ 0

  attributedAmount-other : ∀ event client → ¬ (owner catalog event ≡ client) →
    attributedAmount event client ≡ 0
  attributedAmount-other event client distinct with discreteFin (owner catalog event) client
  ... | yes equality = Empty.rec (distinct equality)
  ... | no different = refl

  paid : Ledger → Fin clients → ℚ
  paid ledger client = sumℚ (λ event → credited (ledger event) (attributedAmount event client))

  -- This bridge supplies Cauchy-real controllers with exactly the finite sum
  -- of the event amounts selected by the ledger and the fixed client owner.
  paid-accounting : ∀ ledger client → rat (paid ledger client)
    ≡ sum (λ event → rat (credited (ledger event) (attributedAmount event client)))
  paid-accounting ledger client =
    rat-sumℚ (λ event → credited (ledger event) (attributedAmount event client))

  paid-empty : ∀ client → paid emptyLedger client ≡ 0
  paid-empty client = sumℚ-zero events

  paid-nonnegative : ∀ ledger client → 0 ℚ.≤ paid ledger client
  paid-nonnegative ledger client = sumℚ-nonnegative _ λ event →
    credited-nonnegative (ledger event) (attributedAmount event client)
      (attributedAmount-nonnegative event client)

  paid-monotone : ∀ before after → SeenIn before after →
    ∀ client → paid before client ℚ.≤ paid after client
  paid-monotone before after extension client = sumℚ-monotone _ _ λ event →
    credited-monotone (before event) (after event) (attributedAmount event client)
      (attributedAmount-nonnegative event client) (extension event)

  paid-ingest-monotone : ∀ ledger event client → paid ledger client ℚ.≤ paid (ingest ledger event) client
  paid-ingest-monotone ledger event = paid-monotone ledger (ingest ledger event)
    (ingest-preserves-seen ledger event)

  paid-ingest-other-client : ∀ ledger event client → ¬ (owner catalog event ≡ client) →
    paid (ingest ledger event) client ≡ paid ledger client
  paid-ingest-other-client ledger event client not-owner = sumℚ-cong _ _ pointwise
    where
    pointwise : ∀ query →
      credited (ingest ledger event query) (attributedAmount query client)
        ≡ credited (ledger query) (attributedAmount query client)
    pointwise query with discreteFin event query
    ... | yes equality =
      amount-zero
      ∙ sym (credited-zero (ledger query))
      ∙ cong (credited (ledger query)) (sym amount-zero)
      where
      amount-zero : attributedAmount query client ≡ 0
      amount-zero = subst (λ id → attributedAmount id client ≡ 0) equality
        (attributedAmount-other event client not-owner)
    ... | no distinct = refl

  paid-ingest-idempotent : ∀ ledger event →
    paid (ingest (ingest ledger event) event) ≡ paid (ingest ledger event)
  paid-ingest-idempotent ledger event = cong paid (ingest-idempotent ledger event)

  paid-ingest-commutes : ∀ ledger first second →
    paid (ingest (ingest ledger first) second) ≡ paid (ingest (ingest ledger second) first)
  paid-ingest-commutes ledger first second = cong paid (ingest-commutes ledger first second)

  -- Replaying any event already present is inert, even if other events
  -- were processed between its first occurrence and this replay.
  ingest-seen : ∀ ledger event → ledger event ≡ true → ingest ledger event ≡ ledger
  ingest-seen ledger event seen = funExt pointwise
    where
    pointwise : ∀ query → ingest ledger event query ≡ ledger query
    pointwise query with discreteFin event query
    ... | yes equality = sym (subst (λ id → ledger id ≡ true) equality seen)
    ... | no distinct = refl

  ingestBatch : Ledger → Batch → Ledger
  ingestBatch ledger [] = ledger
  ingestBatch ledger (event ∷ rest) = ingestBatch (ingest ledger event) rest

  batchMask : Batch → Ledger
  batchMask [] = emptyLedger
  batchMask (event ∷ rest) query = eventMask event query or batchMask rest query

  -- Closed form: after processing a batch, an event is seen precisely when
  -- it was already seen or occurs in the batch's identity mask.
  ingestBatch-closed : ∀ ledger batch →
    ingestBatch ledger batch ≡ (λ query → batchMask batch query or ledger query)
  ingestBatch-closed ledger [] = refl
  ingestBatch-closed ledger (event ∷ rest) =
    ingestBatch-closed (ingest ledger event) rest
    ∙ funExt (λ query → or-swap (batchMask rest query) (eventMask event query) (ledger query)
      ∙ or-assoc (eventMask event query) (batchMask rest query) (ledger query))

  ingestBatch-preserves-seen : ∀ ledger batch → SeenIn ledger (ingestBatch ledger batch)
  ingestBatch-preserves-seen ledger [] query seen = seen
  ingestBatch-preserves-seen ledger (event ∷ rest) query seen =
    ingestBatch-preserves-seen (ingest ledger event) rest query
      (ingest-preserves-seen ledger event query seen)

  paid-ingestBatch-monotone : ∀ ledger batch client →
    paid ledger client ℚ.≤ paid (ingestBatch ledger batch) client
  paid-ingestBatch-monotone ledger batch =
    paid-monotone ledger (ingestBatch ledger batch) (ingestBatch-preserves-seen ledger batch)

  ingestBatch-append : ∀ ledger first second →
    ingestBatch ledger (first ++ second) ≡ ingestBatch (ingestBatch ledger first) second
  ingestBatch-append ledger [] second = refl
  ingestBatch-append ledger (event ∷ rest) second =
    ingestBatch-append (ingest ledger event) rest second

  -- Whole-batch replay is idempotent, including batches containing duplicates.
  ingestBatch-replay : ∀ ledger batch →
    ingestBatch (ingestBatch ledger batch) batch ≡ ingestBatch ledger batch
  ingestBatch-replay ledger batch = ingestBatch-closed (ingestBatch ledger batch) batch
    ∙ funExt (λ query → cong (batchMask batch query or_)
        (funExt⁻ (ingestBatch-closed ledger batch) query)
      ∙ or-repeat (batchMask batch query) (ledger query))
    ∙ sym (ingestBatch-closed ledger batch)

  ingestBatch-repeat : ∀ ledger batch →
    ingestBatch ledger (batch ++ batch) ≡ ingestBatch ledger batch
  ingestBatch-repeat ledger batch = ingestBatch-append ledger batch batch ∙ ingestBatch-replay ledger batch

  ingestBatch-commutes : ∀ ledger first second →
    ingestBatch (ingestBatch ledger first) second ≡ ingestBatch (ingestBatch ledger second) first
  ingestBatch-commutes ledger first second =
    ingestBatch-closed (ingestBatch ledger first) second
    ∙ funExt (λ query → cong (batchMask second query or_)
        (funExt⁻ (ingestBatch-closed ledger first) query)
      ∙ or-swap (batchMask second query) (batchMask first query) (ledger query)
      ∙ cong (batchMask first query or_)
        (sym (funExt⁻ (ingestBatch-closed ledger second) query)))
    ∙ sym (ingestBatch-closed (ingestBatch ledger second) first)

  ingestBatch-swap : ∀ ledger first second →
    ingestBatch ledger (first ++ second) ≡ ingestBatch ledger (second ++ first)
  ingestBatch-swap ledger first second = ingestBatch-append ledger first second
    ∙ ingestBatch-commutes ledger first second ∙ sym (ingestBatch-append ledger second first)

  -- The only batch property used by the final state is its event-ID mask.
  -- An equality witness may justify arbitrary reorderings or duplicate removal.
  ingestBatch-same-events : ∀ ledger first second →
    (∀ event → batchMask first event ≡ batchMask second event) →
    ingestBatch ledger first ≡ ingestBatch ledger second
  ingestBatch-same-events ledger first second same = ingestBatch-closed ledger first
    ∙ funExt (λ query → cong (_or ledger query) (same query))
    ∙ sym (ingestBatch-closed ledger second)

  paid-ingestBatch-replay : ∀ ledger batch →
    paid (ingestBatch (ingestBatch ledger batch) batch) ≡ paid (ingestBatch ledger batch)
  paid-ingestBatch-replay ledger batch = cong paid (ingestBatch-replay ledger batch)

  paid-ingestBatch-swap : ∀ ledger first second →
    paid (ingestBatch ledger (first ++ second)) ≡ paid (ingestBatch ledger (second ++ first))
  paid-ingestBatch-swap ledger first second = cong paid (ingestBatch-swap ledger first second)

  paid-ingestBatch-same-events : ∀ ledger first second →
    (∀ event → batchMask first event ≡ batchMask second event) →
    paid (ingestBatch ledger first) ≡ paid (ingestBatch ledger second)
  paid-ingestBatch-same-events ledger first second same = cong paid
    (ingestBatch-same-events ledger first second same)

  -- Incremental accounting sums over catalog IDs, not received-message
  -- occurrences. An event contributes only if new relative to the old ledger.
  newlyPaid : Ledger → Batch → Fin clients → ℚ
  newlyPaid ledger batch client = sumℚ (λ event →
    credited (batchMask batch event and not (ledger event)) (attributedAmount event client))

  newlyPaid-nonnegative : ∀ ledger batch client → 0 ℚ.≤ newlyPaid ledger batch client
  newlyPaid-nonnegative ledger batch client = sumℚ-nonnegative _ λ event →
    credited-nonnegative (batchMask batch event and not (ledger event)) (attributedAmount event client)
      (attributedAmount-nonnegative event client)

  paid-ingestBatch-decomposition : ∀ ledger batch client →
    paid (ingestBatch ledger batch) client ≡ paid ledger client ℚ.+ newlyPaid ledger batch client
  paid-ingestBatch-decomposition ledger batch client =
    cong (λ state → paid state client) (ingestBatch-closed ledger batch)
    ∙ sumℚ-cong _ _ (λ event → credited-union (ledger event) (batchMask batch event)
        (attributedAmount event client))
    ∙ sumℚ-add (λ event → credited (ledger event) (attributedAmount event client))
      (λ event → credited (batchMask batch event and not (ledger event))
        (attributedAmount event client))

  paid-ingestBatch-accounting : ∀ ledger batch client →
    rat (paid (ingestBatch ledger batch) client)
      ≡ rat (paid ledger client) +ᵣ rat (newlyPaid ledger batch client)
  paid-ingestBatch-accounting ledger batch client =
    cong rat (paid-ingestBatch-decomposition ledger batch client) ∙ sym (+ᵣ-rat _ _)

  -- Event batches affecting other owners cannot change this client's balance.
  paid-ingestBatch-other-client : ∀ ledger batch client →
    (∀ event → batchMask batch event ≡ true → ¬ (owner catalog event ≡ client)) →
    paid (ingestBatch ledger batch) client ≡ paid ledger client
  paid-ingestBatch-other-client ledger batch client unrelated =
    cong (λ state → paid state client) (ingestBatch-closed ledger batch)
    ∙ sumℚ-cong _ _ pointwise
    where
    amount-zero : ∀ event → batchMask batch event ≡ true → attributedAmount event client ≡ 0
    amount-zero event included = attributedAmount-other event client (unrelated event included)

    at-bit : ∀ event bit → batchMask batch event ≡ bit →
      credited (bit or ledger event) (attributedAmount event client)
        ≡ credited (ledger event) (attributedAmount event client)
    at-bit event false included = refl
    at-bit event true included = amount-zero event included
      ∙ sym (credited-zero (ledger event))
      ∙ cong (credited (ledger event)) (sym (amount-zero event included))

    pointwise : ∀ event →
      credited (batchMask batch event or ledger event) (attributedAmount event client)
        ≡ credited (ledger event) (attributedAmount event client)
    pointwise event = at-bit event (batchMask batch event) refl
