{-# OPTIONS --safe #-}

module Cubical.Relation.Binary.Order.Quoset.Interval where

{- Open intervals need only a strict poset. Half-open intervals and their
   inclusions additionally take a nonstrict order and the three compatibility
   laws relating the two orders. -}

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Data.Sigma

open import Cubical.Relation.Binary.Order.Poset.Base
open import Cubical.Relation.Binary.Order.Poset.Interval
open import Cubical.Relation.Binary.Order.Quoset.Base

private
  variable
    ℓ ℓ≤ ℓ< : Level


module _ (Q' : Quoset ℓ ℓ<) where
  private
    Q = ⟨ Q' ⟩

  open QuosetStr (Q' .snd)

  module _ (a b : Q) where
    OpenIntervalPredicate : Q → hProp ℓ<
    OpenIntervalPredicate z = (a < z) × (z < b) ,
      isProp× (is-prop-valued _ _) (is-prop-valued _ _)

    OpenIntervalSubtype : Type (ℓ-max ℓ ℓ<)
    OpenIntervalSubtype = Σ[ z ∈ Q ] ⟨ OpenIntervalPredicate z ⟩


module _
  {P : Type ℓ}
  (P≤ : PosetStr ℓ≤ P)
  (P< : QuosetStr ℓ< P)
  where

  private
    module P≤ = PosetStr P≤
    module P< = QuosetStr P<

    Poset' : Poset ℓ ℓ≤
    Poset' = P , P≤

    Quoset' : Quoset ℓ ℓ<
    Quoset' = P , P<

  LeftClosedRightOpenIntervalPredicate : P → P → P → hProp (ℓ-max ℓ≤ ℓ<)
  LeftClosedRightOpenIntervalPredicate a b z =
    (a P≤.≤ z) × (z P<.< b) ,
    isProp× (P≤.is-prop-valued _ _) (P<.is-prop-valued _ _)

  LeftOpenRightClosedIntervalPredicate : P → P → P → hProp (ℓ-max ℓ≤ ℓ<)
  LeftOpenRightClosedIntervalPredicate a b z =
    (a P<.< z) × (z P≤.≤ b) ,
    isProp× (P<.is-prop-valued _ _) (P≤.is-prop-valued _ _)

  module _
    (<-≤-weaken : ∀ x y → x P<.< y → x P≤.≤ y)
    (<-≤-trans : ∀ x y z → x P<.< y → y P≤.≤ z → x P<.< z)
    (≤-<-trans : ∀ x y z → x P≤.≤ y → y P<.< z → x P<.< z)
    where

    openIntervalPredicate⊆ : ∀ {a b a' b'}
      → a' P≤.≤ a → b P≤.≤ b'
      → ∀ z
      → ⟨ OpenIntervalPredicate Quoset' a b z ⟩
      → ⟨ OpenIntervalPredicate Quoset' a' b' z ⟩
    openIntervalPredicate⊆ {a} {b} {a'} {b'} a'≤a b≤b' z (a<z , z<b) =
      ≤-<-trans a' a z a'≤a a<z , <-≤-trans z b b' z<b b≤b'

    openIntervalPredicate⊆intervalPredicate : ∀ a b z
      → ⟨ OpenIntervalPredicate Quoset' a b z ⟩
      → ⟨ IntervalPredicate Poset' a b z ⟩
    openIntervalPredicate⊆intervalPredicate a b z (a<z , z<b) =
      <-≤-weaken a z a<z , <-≤-weaken z b z<b

    intervalPredicate⊆openIntervalPredicate : ∀ a' b' a b
      → a P<.< a' → b' P<.< b
      → ∀ z
      → ⟨ IntervalPredicate Poset' a' b' z ⟩
      → ⟨ OpenIntervalPredicate Quoset' a b z ⟩
    intervalPredicate⊆openIntervalPredicate a' b' a b a<a' b'<b z (a'≤z , z≤b') =
      <-≤-trans a a' z a<a' a'≤z , ≤-<-trans z b' b z≤b' b'<b

    openIntervalPredicate⊆leftClosedRightOpenIntervalPredicate : ∀ a b z
      → ⟨ OpenIntervalPredicate Quoset' a b z ⟩
      → ⟨ LeftClosedRightOpenIntervalPredicate a b z ⟩
    openIntervalPredicate⊆leftClosedRightOpenIntervalPredicate a b z (a<z , z<b) =
      <-≤-weaken a z a<z , z<b

    openIntervalPredicate⊆leftOpenRightClosedIntervalPredicate : ∀ a b z
      → ⟨ OpenIntervalPredicate Quoset' a b z ⟩
      → ⟨ LeftOpenRightClosedIntervalPredicate a b z ⟩
    openIntervalPredicate⊆leftOpenRightClosedIntervalPredicate a b z (a<z , z<b) =
      a<z , <-≤-weaken z b z<b

    leftClosedRightOpenIntervalPredicate⊆intervalPredicate : ∀ a b z
      → ⟨ LeftClosedRightOpenIntervalPredicate a b z ⟩
      → ⟨ IntervalPredicate Poset' a b z ⟩
    leftClosedRightOpenIntervalPredicate⊆intervalPredicate a b z (a≤z , z<b) =
      a≤z , <-≤-weaken z b z<b

    leftOpenRightClosedIntervalPredicate⊆intervalPredicate : ∀ a b z
      → ⟨ LeftOpenRightClosedIntervalPredicate a b z ⟩
      → ⟨ IntervalPredicate Poset' a b z ⟩
    leftOpenRightClosedIntervalPredicate⊆intervalPredicate a b z (a<z , z≤b) =
      <-≤-weaken a z a<z , z≤b

    leftClosedRightOpenIntervalPredicate⊆ : ∀ {a b a' b'}
      → a' P≤.≤ a → b P≤.≤ b'
      → ∀ z
      → ⟨ LeftClosedRightOpenIntervalPredicate a b z ⟩
      → ⟨ LeftClosedRightOpenIntervalPredicate a' b' z ⟩
    leftClosedRightOpenIntervalPredicate⊆ {a} {b} {a'} {b'} a'≤a b≤b' z (a≤z , z<b) =
      P≤.is-trans a' a z a'≤a a≤z , <-≤-trans z b b' z<b b≤b'

    leftOpenRightClosedIntervalPredicate⊆ : ∀ {a b a' b'}
      → a' P≤.≤ a → b P≤.≤ b'
      → ∀ z
      → ⟨ LeftOpenRightClosedIntervalPredicate a b z ⟩
      → ⟨ LeftOpenRightClosedIntervalPredicate a' b' z ⟩
    leftOpenRightClosedIntervalPredicate⊆ {a} {b} {a'} {b'} a'≤a b≤b' z (a<z , z≤b) =
      ≤-<-trans a' a z a'≤a a<z , P≤.is-trans z b b' z≤b b≤b'
