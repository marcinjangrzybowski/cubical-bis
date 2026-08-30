module Cubical.Analysis.Real.Sequence.Eventually where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function

open import Cubical.Data.Nat as ℕ using (ℕ)
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Premetric.Properties
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Product

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Algebra.Lattice.Base
open import Cubical.Analysis.Real.Order.Base
open import Cubical.Analysis.Real.Order.Strict.Base
open import Cubical.Analysis.Real.Order.Strict.Properties
open import Cubical.Analysis.Real.Sequence


private
  module ℝTheory = PremetricTheory ℝPremetricSpace

  ℝ²PremetricSpace =
    PremetricProduct ℝPremetricSpace ℝPremetricSpace


EventuallyEqualTail :
  (ℕ → ℝ) → (ℕ → ℝ) → Type₀
EventuallyEqualTail x y =
  Σ[ N ∈ ℕ ] (∀ n → N ℕ.≤ n → x n ≡ y n)


EventuallyEqualSequence :
  (ℕ → ℝ) → (ℕ → ℝ) → Type₀
EventuallyEqualSequence x y =
  ∥ EventuallyEqualTail x y ∥₁


isPropEventuallyEqualSequence : ∀ x y →
  isProp (EventuallyEqualSequence x y)
isPropEventuallyEqualSequence x y = squash₁


eventuallyEqualRefl : ∀ x →
  EventuallyEqualSequence x x
eventuallyEqualRefl x =
  ∣ 0 , (λ _ _ → refl) ∣₁


eventuallyEqualSym : ∀ {x y} →
  EventuallyEqualSequence x y →
  EventuallyEqualSequence y x
eventuallyEqualSym = PT.map λ where
  (N , equal) → N , λ n N≤n → sym (equal n N≤n)


eventuallyEqualTrans : ∀ {x y z} →
  EventuallyEqualSequence x y →
  EventuallyEqualSequence y z →
  EventuallyEqualSequence x z
eventuallyEqualTrans {x} {y} {z} x≡y y≡z =
  PT.map2 combine x≡y y≡z
  where
  combine : EventuallyEqualTail x y →
    EventuallyEqualTail y z → EventuallyEqualTail x z
  combine (K , left) (L , right) =
    ℕ.max K L , λ n max≤n →
      left n
        (ℕ.≤-trans
          (ℕ.left-≤-max {m = K} {n = L}) max≤n)
      ∙ right n
        (ℕ.≤-trans
          (ℕ.right-≤-max {n = L} {m = K}) max≤n)


pointwiseEqual→eventuallyEqual : ∀ {x y} →
  (∀ n → x n ≡ y n) →
  EventuallyEqualSequence x y
pointwiseEqual→eventuallyEqual pointwise =
  ∣ 0 , (λ n _ → pointwise n) ∣₁


eventuallyEqualPresSeqWitness : ∀ {x y} →
  EventuallyEqualSequence x y →
  SeqWitness x → SeqWitness y
eventuallyEqualPresSeqWitness {x} {y} eventually gx =
  PT.rec squash₁ withCutoff eventually
  where
  withCutoff : EventuallyEqualTail x y → SeqWitness y
  withCutoff equal =
    PT.map
      (ℝTheory.eventuallyEqualSeqPresIsCauchySeq x y equal)
      gx


eventuallyEqualPresIsLimitSequence : ∀ {x y l} →
  EventuallyEqualSequence x y →
  isLimitSequence x l → isLimitSequence y l
eventuallyEqualPresIsLimitSequence {x} {y} {l}
    eventually x→l =
  PT.rec (isPropIsLimitSequence y l)
    (λ equal →
      ℝTheory.eventuallyEqualSeqPresIsLimitSeq
        x y l equal x→l)
    eventually


EventuallyLeTail :
  (ℕ → ℝ) → (ℕ → ℝ) → Type₀
EventuallyLeTail x y =
  Σ[ N ∈ ℕ ] (∀ n → N ℕ.≤ n → x n ≤ℝ y n)


EventuallyLeSequence :
  (ℕ → ℝ) → (ℕ → ℝ) → Type₀
EventuallyLeSequence x y =
  ∥ EventuallyLeTail x y ∥₁


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
        (left n
          (ℕ.≤-trans
            (ℕ.left-≤-max {m = K} {n = L}) max≤n))
        (right n
          (ℕ.≤-trans
            (ℕ.right-≤-max {n = L} {m = K}) max≤n))


eventuallyEqual→eventuallyLe : ∀ {x y} →
  EventuallyEqualSequence x y →
  EventuallyLeSequence x y
eventuallyEqual→eventuallyLe {x} {y} = PT.map λ where
  (N , equal) →
    N , λ n N≤n →
      subst (x n ≤ℝ_) (equal n N≤n) (≤ℝ-refl (x n))


pointwiseLe→eventuallyLe : ∀ {x y} →
  (∀ n → x n ≤ℝ y n) →
  EventuallyLeSequence x y
pointwiseLe→eventuallyLe pointwise =
  ∣ 0 , (λ n _ → pointwise n) ∣₁


maxPresIsLimitSequence : ∀ {x y l m} →
  isLimitSequence x l → isLimitSequence y m →
  isLimitSequence
    (λ n → maxℝ (x n) (y n))
    (maxℝ l m)
maxPresIsLimitSequence {x} {y} {l} {m} x→l y→m =
  continuousBinaryPreservesIsLimitSequence
    (uncurry maxℝ)
    (maxOfContinuousIsContinuous
      (ℝ²PremetricSpace .snd)
      fst snd (snd productFstC) (snd productSndC))
    x→l y→m


eventuallyLePresLimits : ∀ {x y l m} →
  EventuallyLeSequence x y →
  isLimitSequence x l → isLimitSequence y m →
  l ≤ℝ m
eventuallyLePresLimits {x} {y} {l} {m}
    eventually x→l y→m =
  PT.rec (isProp≤ℝ l m) withCutoff eventually
  where
  maximum : ℕ → ℝ
  maximum n = maxℝ (x n) (y n)

  maximum→maximum-limit :
    isLimitSequence maximum (maxℝ l m)
  maximum→maximum-limit =
    maxPresIsLimitSequence
      {x = x} {y = y} {l = l} {m = m} x→l y→m

  withCutoff : EventuallyLeTail x y → l ≤ℝ m
  withCutoff (N , ordered) =
    cong fst
      (isPropSequenceLimit y
        (maxℝ l m , maximum-limit-as-y-limit)
        (m , y→m))
    where
    maximum-eventually-y :
      EventuallyEqualSequence maximum y
    maximum-eventually-y = ∣ N , ordered ∣₁

    maximum-limit-as-y-limit :
      isLimitSequence y (maxℝ l m)
    maximum-limit-as-y-limit =
      eventuallyEqualPresIsLimitSequence
        {x = maximum} {y = y} {l = maxℝ l m}
        maximum-eventually-y maximum→maximum-limit


pointwiseLePresLimits : ∀ {x y l m} →
  (∀ n → x n ≤ℝ y n) →
  isLimitSequence x l → isLimitSequence y m →
  l ≤ℝ m
pointwiseLePresLimits {x} {y} {l} {m} pointwise x→l y→m =
  eventuallyLePresLimits
    {x = x} {y = y} {l = l} {m = m}
    (pointwiseLe→eventuallyLe {x = x} {y = y} pointwise)
    x→l y→m


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


EventuallyLtTail :
  (ℕ → ℝ) → (ℕ → ℝ) → Type₀
EventuallyLtTail x y =
  Σ[ N ∈ ℕ ] (∀ n → N ℕ.≤ n → x n <ℝ y n)


EventuallyLtSequence :
  (ℕ → ℝ) → (ℕ → ℝ) → Type₀
EventuallyLtSequence x y =
  ∥ EventuallyLtTail x y ∥₁


isPropEventuallyLtSequence : ∀ x y →
  isProp (EventuallyLtSequence x y)
isPropEventuallyLtSequence x y = squash₁


eventuallyLt→eventuallyLe : ∀ {x y} →
  EventuallyLtSequence x y → EventuallyLeSequence x y
eventuallyLt→eventuallyLe {x} {y} = PT.map λ where
  (N , strict) →
    N , λ n N≤n →
      <ℝ-weaken (x n) (y n) (strict n N≤n)


eventuallyLtPresLimitsLe : ∀ {x y l m} →
  EventuallyLtSequence x y →
  isLimitSequence x l → isLimitSequence y m →
  l ≤ℝ m
eventuallyLtPresLimitsLe {x} {y} {l} {m} strict x→l y→m =
  eventuallyLePresLimits
    {x = x} {y = y} {l = l} {m = m}
    (eventuallyLt→eventuallyLe {x = x} {y = y} strict)
    x→l y→m
