module Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Sequence.Order where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals
  as Real
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Sequence.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Analysis.Sequence.Operations
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Lattice.Laws
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Base
open import Cubical.Relation.Premetric.Completion.CauchySequence.Reals.Algebra.Order.Strict.Base


-- Eventual order ---------------------------------------------------------
--
-- The established sequence API carries a chosen cutoff.  None of the order
-- consequences below needs to inspect that cutoff computationally, so the
-- public relation stores only its mere existence.  This makes the premise
-- strictly easier to construct and is stable under all propositional uses.

EventuallyLeTail :
  (ℕ → Real.ℝ) → (ℕ → Real.ℝ) → Type₀
EventuallyLeTail x y =
  Σ[ N ∈ ℕ ] (∀ n → N ℕ.≤ n → x n ≤ℝ y n)


EventuallyLeSequence :
  (ℕ → Real.ℝ) → (ℕ → Real.ℝ) → Type₀
EventuallyLeSequence x y = ∥ EventuallyLeTail x y ∥₁


isPropEventuallyLeSequence : ∀ x y →
  isProp (EventuallyLeSequence x y)
isPropEventuallyLeSequence x y = squash₁


eventuallyLeRefl : ∀ x → EventuallyLeSequence x x
eventuallyLeRefl x =
  ∣ 0 , (λ n _ → ≤ℝ-refl (x n)) ∣₁


eventuallyLeTrans : ∀ {x y z} →
  EventuallyLeSequence x y →
  EventuallyLeSequence y z →
  EventuallyLeSequence x z
eventuallyLeTrans {x} {y} {z} x≤y y≤z =
  PT.map2 combine x≤y y≤z
  where
  combine : EventuallyLeTail x y →
    EventuallyLeTail y z → EventuallyLeTail x z
  combine (K , left) (L , right) =
    ℕ.max K L , λ n max≤n →
      ≤ℝ-trans (x n) (y n) (z n)
        (left n (ℕ.≤-trans
          (ℕ.left-≤-max {m = K} {n = L}) max≤n))
        (right n (ℕ.≤-trans
          (ℕ.right-≤-max {n = L} {m = K}) max≤n))


eventuallyEqual→eventuallyLe : ∀ {x y} →
  EventuallyEqualSequence x y → EventuallyLeSequence x y
eventuallyEqual→eventuallyLe {x} {y} = PT.map λ where
  (N , equal) →
    N , λ n N≤n →
      subst (x n ≤ℝ_) (equal n N≤n) (≤ℝ-refl (x n))


pointwiseLe→eventuallyLe : ∀ {x y} →
  (∀ n → x n ≤ℝ y n) → EventuallyLeSequence x y
pointwiseLe→eventuallyLe pointwise =
  ∣ 0 , (λ n _ → pointwise n) ∣₁


-- Closedness of order under sequential limits ---------------------------
--
-- If `x n ≤ y n` eventually, then `max (x n) (y n)` is eventually equal
-- to `y n`.  Its limit is both `max l m`, by continuity/computation of max,
-- and `m`, by eventual equality.  Uniqueness therefore yields `l ≤ m`.

eventuallyLePresLimits : ∀ {x y l m} →
  EventuallyLeSequence x y →
  isLimitSequence x l → isLimitSequence y m →
  l ≤ℝ m
eventuallyLePresLimits {x} {y} {l} {m} eventually x→l y→m =
  PT.rec (isProp≤ℝ l m) with-cutoff eventually
  where
  maximum : ℕ → Real.ℝ
  maximum n = x n ⊔ℝ y n

  maximum→maximum-limit : isLimitSequence maximum (l ⊔ℝ m)
  maximum→maximum-limit =
    maxPresIsLimitSequence
      {x = x} {y = y} {l = l} {m = m} x→l y→m

  with-cutoff : EventuallyLeTail x y → l ≤ℝ m
  with-cutoff (N , ordered) =
    cong fst
      (isPropSequenceLimit y
        (l ⊔ℝ m , maximum-limit-as-y-limit)
        (m , y→m))
    where
    maximum-eventually-y : EventuallyEqualSequence maximum y
    maximum-eventually-y = ∣ N , ordered ∣₁

    maximum-limit-as-y-limit : isLimitSequence y (l ⊔ℝ m)
    maximum-limit-as-y-limit =
      eventuallyEqualPresIsLimitSequence
        maximum-eventually-y maximum→maximum-limit


pointwiseLePresLimits : ∀ {x y l m} →
  (∀ n → x n ≤ℝ y n) →
  isLimitSequence x l → isLimitSequence y m →
  l ≤ℝ m
pointwiseLePresLimits {x} {y} {l} {m} pointwise x→l y→m =
  eventuallyLePresLimits
    {x = x} {y = y} {l = l} {m = m}
    (pointwiseLe→eventuallyLe {x = x} {y = y} pointwise) x→l y→m


eventuallyUpperBoundPresLimit : ∀ {x l b} →
  EventuallyLeSequence x (λ _ → b) →
  isLimitSequence x l → l ≤ℝ b
eventuallyUpperBoundPresLimit {x} {l} {b} bounded x→l =
  eventuallyLePresLimits
    {x = x} {y = λ _ → b} {l = l} {m = b}
    bounded x→l (constantIsLimitSequence b)


eventuallyLowerBoundPresLimit : ∀ {x l b} →
  EventuallyLeSequence (λ _ → b) x →
  isLimitSequence x l → b ≤ℝ l
eventuallyLowerBoundPresLimit {x} {l} {b} bounded x→l =
  eventuallyLePresLimits
    {x = λ _ → b} {y = x} {l = b} {m = l}
    bounded (constantIsLimitSequence b) x→l


-- Eventual strict order can only yield a non-strict inequality of limits:
-- the positive gaps may vanish.  Its cutoff is again merely present.

EventuallyLtTail :
  (ℕ → Real.ℝ) → (ℕ → Real.ℝ) → Type₀
EventuallyLtTail x y =
  Σ[ N ∈ ℕ ] (∀ n → N ℕ.≤ n → x n <ℝ y n)


EventuallyLtSequence :
  (ℕ → Real.ℝ) → (ℕ → Real.ℝ) → Type₀
EventuallyLtSequence x y = ∥ EventuallyLtTail x y ∥₁


eventuallyLt→eventuallyLe : ∀ {x y} →
  EventuallyLtSequence x y → EventuallyLeSequence x y
eventuallyLt→eventuallyLe {x} {y} = PT.map λ where
  (N , strict) →
    N , λ n N≤n → <ℝ-weaken (x n) (y n) (strict n N≤n)


eventuallyLtPresLimitsLe : ∀ {x y l m} →
  EventuallyLtSequence x y →
  isLimitSequence x l → isLimitSequence y m →
  l ≤ℝ m
eventuallyLtPresLimitsLe {x} {y} {l} {m} strict x→l y→m =
  eventuallyLePresLimits
    {x = x} {y = y} {l = l} {m = m}
    (eventuallyLt→eventuallyLe strict) x→l y→m
