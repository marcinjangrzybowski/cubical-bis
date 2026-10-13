module Cubical.Analysis.Real.Sequence.Uniform where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open PositiveRationals using (ℚ₊)
open import Cubical.Relation.Premetric.Base

open import Cubical.Analysis.Real.Base
open import Cubical.Analysis.Real.Sequence

-- The tail index works simultaneously at every point of the domain.
IsUniformLimit : ∀ {ℓ} {A : Type ℓ} → (ℕ → A → ℝ) → (A → ℝ) → Type ℓ
IsUniformLimit functions limit =
  ∀ ε → ∃[ N ∈ ℕ ] (∀ n → N ℕ.≤ n → ∀ x → functions n x ∼[ ε ] limit x)

isPropIsUniformLimit : ∀ {ℓ} {A : Type ℓ} (functions : ℕ → A → ℝ) limit →
  isProp (IsUniformLimit functions limit)
isPropIsUniformLimit functions limit = isPropΠ λ _ → squash₁

IsUniformLimitWith : ∀ {ℓ} {A : Type ℓ} →
  (ℕ → A → ℝ) → (A → ℝ) → (ℚ₊ → ℕ) → Type ℓ
IsUniformLimitWith functions limit μ =
  ∀ ε n → μ ε ℕ.≤ n → ∀ x → functions n x ∼[ ε ] limit x

-- This stronger hypothesis is used only when constructing a new sequential
-- completion value. It is never inferred from separately truncated tails.
UniformLimitWitness : ∀ {ℓ} {A : Type ℓ} → (ℕ → A → ℝ) → (A → ℝ) → Type ℓ
UniformLimitWitness functions limit = ∃[ μ ∈ (ℚ₊ → ℕ) ] IsUniformLimitWith functions limit μ

uniformLimitWitness→uniformLimit : ∀ {ℓ} {A : Type ℓ}
  (functions : ℕ → A → ℝ) limit → UniformLimitWitness functions limit → IsUniformLimit functions limit
uniformLimitWitness→uniformLimit functions limit witness ε =
  PT.map (λ { (μ , close) → μ ε , close ε }) witness

uniformLimitAt : ∀ {ℓ} {A : Type ℓ} (functions : ℕ → A → ℝ) limit →
  IsUniformLimit functions limit → ∀ x → isLimitSequence (λ n → functions n x) (limit x)
uniformLimitAt functions limit uniform x ε =
  PT.map (λ { (N , close) → N , λ n large → close n large x }) (uniform ε)

uniformLimitUnique : ∀ {ℓ} {A : Type ℓ} (functions : ℕ → A → ℝ) f g →
  IsUniformLimit functions f → IsUniformLimit functions g → f ≡ g
uniformLimitUnique functions f g first second = funExt λ x →
  limitSequenceUnique (λ n → functions n x) (f x) (g x)
    (uniformLimitAt functions f first x) (uniformLimitAt functions g second x)

uniformLimitPrecompose : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
  (functions : ℕ → A → ℝ) limit (mapping : B → A) →
  IsUniformLimit functions limit → IsUniformLimit (λ n → functions n ∘ mapping) (limit ∘ mapping)
uniformLimitPrecompose functions limit mapping uniform ε =
  PT.map (λ { (N , close) → N , λ n large x → close n large (mapping x) }) (uniform ε)
