open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.Alternative.Experimental.TruncatedScalePrototype
  {ℓ} {ℓ'} (M' : PremetricSpace ℓ ℓ') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Relation.Premetric.Completion.Alternative M'

open PositiveRationals
open Γ

private
  M = M' .fst
  module PM = PremetricStr (M' .snd)


-- Early prototype of the now-established TruncatedScale presentation.  Only
-- the partial signature is kept here, documenting the intermediate design
-- without confusing it with the completed construction.

data ℭ̂' : Type (ℓ-max ℓ ℓ')
data _∼̂'[_]_ : ℭ̂' → ℚ₊ → ℭ̂' → Type (ℓ-max ℓ ℓ')

𝐆 : (ℚ₊ → ℭ̂') → Type (ℓ-max ℓ ℓ')
𝐆 x = ∃[ g ∈ Γ ]
  (∀ ε δ → x ε ∼̂'[ (g .γ ε) +₊ (g .γ δ) ] x δ)

data ℭ̂' where
  ι   : M → ℭ̂'
  lim : (x : ℚ₊ → ℭ̂') → 𝐆 x → ℭ̂'
  eqℭ : ∀ x y → (∀ ε → x ∼̂'[ ε ] y) → x ≡ y

data _∼̂'[_]_ where
  ι-ι : ∀ x y ε → x PM.≈[ ε ] y → ι x ∼̂'[ ε ] ι y

  -- The intended mixed and limit closeness constructors are still under
  -- investigation.  They remain documented here without becoming part of
  -- the stable Alternative.Properties API.
  --
  -- ι-lim   : ∀ x y g ε δ yc Δ
  --           → ι x ∼̂'[ ε -₊ (g .γ δ) , Δ ] y δ
  --           → ι x ∼̂'[ ε ] lim y g yc
  -- lim-ι   : ∀ x g y ε δ xc Δ
  --           → x δ ∼̂'[ ε -₊ (g .γ δ) , Δ ] ι y
  --           → lim x g xc ∼̂'[ ε ] ι y
  -- lim-lim : ∀ x g y g' ε δ η xc yc Δ
  --           → x δ ∼̂'[ ε -₊ ((g .γ δ) +₊ (g' .γ η)) , Δ ] y η
  --           → lim x g xc ∼̂'[ ε ] lim y g' yc

  isProp∼ : ∀ x ε y → isProp (x ∼̂'[ ε ] y)
