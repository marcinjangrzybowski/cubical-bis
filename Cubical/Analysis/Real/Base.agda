module Cubical.Analysis.Real.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Sigma
open import Cubical.Data.Rationals.Base as ℚ
open import Cubical.Data.Rationals.Inverse
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Rationals.Order as ℚ
open import Cubical.Data.Rationals.Order.AbsoluteValue as ℚ
open import Cubical.Data.Rationals.Order.Algebra as ℚ

open import Cubical.Algebra.Ring
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Properties
open import Cubical.Relation.Premetric.Instances.Rationals

import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Base
  as SequentialDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Properties
  as SequentialPropertiesDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Comparison.Regular
  as ComparisonDefinition

module S = SequentialDefinition ℚPremetricSpace
module SP = SequentialPropertiesDefinition ℚPremetricSpace
module Comparison = ComparisonDefinition ℚPremetricSpace

open PositiveRationals
open OrderedCommRingStr (snd ℚOrderedCommRing)
open OrderedCommRingTheory ℚOrderedCommRing


-- The real numbers in Cubical.Analysis are the sequence-backed completion of
-- the ordinary rational premetric.

ℝ : Type₀
ℝ = S.ℭ̂ₛ

rat : ℚ → ℝ
rat = S.ι

infix 4 _∼[_]_

_∼[_]_ : ℝ → ℚ₊ → ℝ → Type₀
_∼[_]_ = S._∼̂ₛ[_]_

CauchySeq : (ℕ → ℝ) → Type₀
CauchySeq = S.CauchySeq

SeqWitness : (ℕ → ℝ) → Type₀
SeqWitness = S.SeqWitness

lim : (x : ℕ → ℝ) → SeqWitness x → ℝ
lim = S.lim

eqℝ : ∀ x y → (∀ ε → x ∼[ ε ] y) → x ≡ y
eqℝ = S.eqℭ

isSetℝ : isSet ℝ
isSetℝ = S.isSetℭ̂ₛ

ℝPremetricSpace : PremetricSpace ℓ-zero ℓ-zero
ℝPremetricSpace = SP.ℭ̂ₛPremetricSpace

rat-rat : ∀ q r ε →
  abs (q ℚ.- r) ℚ.< fst ε → rat q ∼[ ε ] rat r
rat-rat = S.ι-ι

rat-rat-reflects : ∀ q r ε →
  rat q ∼[ ε ] rat r → abs (q ℚ.- r) ℚ.< fst ε
rat-rat-reflects = Comparison.ι-reflects∼

refl∼ : ∀ x ε → x ∼[ ε ] x
refl∼ = S.isRefl∼̂ₛ

private module Pℚ = PremetricStr (ℚPremetricSpace .snd)

rat-injective : ∀ {q r} → rat q ≡ rat r → q ≡ r
rat-injective {q} {r} q≡r = Pℚ.isSeparated≈ q r λ ε →
  rat-rat-reflects q r ε
    (subst (λ z → rat q ∼[ ε ] z) q≡r (refl∼ (rat q) ε))

sym∼ : ∀ x y ε → x ∼[ ε ] y → y ∼[ ε ] x
sym∼ = S.sym∼

triangle∼ : ∀ x y z ε δ →
  x ∼[ ε ] y → y ∼[ δ ] z → x ∼[ ε +₊ δ ] z
triangle∼ = S.tri∼

lim-isLimitSeq : ∀ x gx →
  PremetricTheory.isLimitSeq ℝPremetricSpace x (lim x gx)
lim-isLimitSeq = SP.lim-isLimitSeq

rat-dense : ∀ x ε → ∃[ q ∈ ℚ ] (rat q ∼[ ε ] x)
rat-dense = SP.∃approx
