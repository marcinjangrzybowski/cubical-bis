module Cubical.HITs.CauchyReals.Analysis.Order.Functions where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Powerset

open import Cubical.Relation.Binary.Order.Poset.Mappings using
  (IsIsotoneOn)
open import Cubical.Relation.Binary.Order.Quoset.Mappings using
  (IsStrictlyIsotoneOn)

open import Cubical.HITs.CauchyReals.Foundation.Base
open import Cubical.HITs.CauchyReals.Foundation.Order.Base

IsStrictlyIncreasingOn :
  (P : ℙ ℝ) → (∀ x → x ∈ P → ℝ) → Type
IsStrictlyIncreasingOn P f = IsStrictlyIsotoneOn
  (ℝ<Quoset .snd) P f (ℝ<Quoset .snd)

IsNondecreasingOn :
  (P : ℙ ℝ) → (∀ x → x ∈ P → ℝ) → Type
IsNondecreasingOn P f = IsIsotoneOn
  (ℝ≤Poset .snd) P f (ℝ≤Poset .snd)
