module Cubical.HITs.CauchyReals.Analysis.Order.Functions where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset

open import Cubical.Relation.Binary.Order.Poset.Mappings using
  (IsIsotoneOn)
open import Cubical.Relation.Binary.Order.Poset.Instances.Rationals using
  (ℚ≤Poset)
open import Cubical.Relation.Binary.Order.Quoset.Mappings using
  (IsStrictlyIsotoneOn)
open import Cubical.Relation.Binary.Order.Quoset.Instances.Rationals using
  (ℚ<Quoset)

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base
open import Cubical.HITs.CauchyReals.Foundation.Rationals

IsStrictlyIncreasingOn :
  (P : ℙ ℝ) → (∀ x → x ∈ P → ℝ) → Type
IsStrictlyIncreasingOn P f = IsStrictlyIsotoneOn
  (ℝ<Quoset .snd) P f (ℝ<Quoset .snd)

IsNondecreasingOn :
  (P : ℙ ℝ) → (∀ x → x ∈ P → ℝ) → Type
IsNondecreasingOn P f = IsIsotoneOn
  (ℝ≤Poset .snd) P f (ℝ≤Poset .snd)


isIncrasingℙ : (P : ℙ ℚ) → (∀ x → x ∈ P → ℚ) → Type₀
isIncrasingℙ P f = IsStrictlyIsotoneOn
  (ℚ<Quoset .snd) P f (ℚ<Quoset .snd)


isNondecrasingℙ : (P : ℙ ℚ) → (∀ x → x ∈ P → ℚ) → Type₀
isNondecrasingℙ P f = IsIsotoneOn
  (ℚ≤Poset .snd) P f (ℚ≤Poset .snd)
