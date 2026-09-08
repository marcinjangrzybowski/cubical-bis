{-# OPTIONS --safe --cubical #-}

module Cubical.HITs.CauchyReals.Example.Financial.Margin.Scenario where

open import Cubical.HITs.CauchyReals.Example.Financial.Core.Finite
open import Cubical.Foundations.Equiv using (_≃_; propBiimpl→Equiv)
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Tactics.CommRingSolver.Specialised.Reals

-- A ranges over the admissible states of an arbitrary scenario domain.
-- No enumeration, compactness, supremum, or decidable real order is assumed.
Coverage : ∀ {ℓ ℓ'} {S : Type ℓ} → (S → Type ℓ') →
  (S → ℝ) → (S → ℝ) → ℝ → Type (ℓ-max ℓ ℓ')
Coverage A X C b = ∀ state → A state → X state ≤ᵣ C state +ᵣ b

record MarginCertificate {ℓ ℓ'} {S : Type ℓ} (A : S → Type ℓ')
  (X C : S → ℝ) (m : ℝ) : Type (ℓ-max ℓ ℓ') where
  field
    certificate-nonnegative : 0 ≤ᵣ m
    certificate-coverage : Coverage A X C m
    certificate-least : ∀ b → 0 ≤ᵣ b → Coverage A X C b → m ≤ᵣ b
open MarginCertificate public

certificate-bound→coverage : ∀ {ℓ ℓ'} {S : Type ℓ} {A : S → Type ℓ'}
  {X C : S → ℝ} {m} → MarginCertificate A X C m →
  ∀ b → m ≤ᵣ b → Coverage A X C b
certificate-bound→coverage {C = C} cert b bound state member = isTrans≤ᵣ _ _ _
  (certificate-coverage cert state member) (≤ᵣ-o+ _ _ (C state) bound)

certificate-budget≃coverage : ∀ {ℓ ℓ'} {S : Type ℓ} {A : S → Type ℓ'}
  {X C : S → ℝ} {m} → MarginCertificate A X C m →
  ∀ b → 0 ≤ᵣ b → (m ≤ᵣ b) ≃ Coverage A X C b
certificate-budget≃coverage cert b b₊ = propBiimpl→Equiv
  (isProp≤ᵣ _ _) (isPropΠ2 (λ _ _ → isProp≤ᵣ _ _))
  (certificate-bound→coverage cert b) (certificate-least cert b b₊)

-- In the small scenario universes used by the financial models, the two
-- propositions inhabit the same universe and univalence gives a path.
certificate-policy-path : ∀ {S : Type₀} {A : S → Type₀}
  {X C : S → ℝ} {m} → MarginCertificate A X C m →
  ∀ b → 0 ≤ᵣ b → (m ≤ᵣ b) ≡ Coverage A X C b
certificate-policy-path cert b b₊ = ua (certificate-budget≃coverage cert b b₊)

-- An explicitly supplied binding state proves leastness even for signed
-- budgets. Such a state need not exist when every claim is overcollateralized
-- and the least nonnegative margin is zero.
record BindingScenario {ℓ ℓ'} {S : Type ℓ} (A : S → Type ℓ')
  (X C : S → ℝ) (m : ℝ) : Type (ℓ-max ℓ ℓ') where
  field
    binding-state : S
    binding-admissible : A binding-state
    binding-equation : X binding-state -ᵣ C binding-state ≡ m
open BindingScenario public

coverage-forces-difference : ∀ x c m → x -ᵣ c ≡ m →
  ∀ b → x ≤ᵣ c +ᵣ b → m ≤ᵣ b
coverage-forces-difference x c m equation b coverage = subst2 _≤ᵣ_ equation cancel
  (≤ᵣ-+o _ _ (-ᵣ c) coverage)
  where
  cancel : (c +ᵣ b) -ᵣ c ≡ b
  cancel = ℝ!

binding-least : ∀ {ℓ ℓ'} {S : Type ℓ} {A : S → Type ℓ'}
  {X C : S → ℝ} {m} → BindingScenario A X C m →
  ∀ b → Coverage A X C b → m ≤ᵣ b
binding-least {X = X} {C = C} {m = m} binding b coverage =
  coverage-forces-difference (X (binding-state binding)) (C (binding-state binding)) m
    (binding-equation binding) b
    (coverage (binding-state binding) (binding-admissible binding))

certificate-from-binding : ∀ {ℓ ℓ'} {S : Type ℓ} {A : S → Type ℓ'}
  {X C : S → ℝ} {m} → 0 ≤ᵣ m → Coverage A X C m →
  BindingScenario A X C m → MarginCertificate A X C m
certificate-from-binding m₊ coverage binding .certificate-nonnegative = m₊
certificate-from-binding m₊ coverage binding .certificate-coverage = coverage
certificate-from-binding m₊ coverage binding .certificate-least b b₊ = binding-least binding b

binding-budget≃coverage : ∀ {ℓ ℓ'} {S : Type ℓ} {A : S → Type ℓ'}
  {X C : S → ℝ} {m} → MarginCertificate A X C m → BindingScenario A X C m →
  ∀ b → (m ≤ᵣ b) ≃ Coverage A X C b
binding-budget≃coverage cert binding b = propBiimpl→Equiv
  (isProp≤ᵣ _ _) (isPropΠ2 (λ _ _ → isProp≤ᵣ _ _))
  (certificate-bound→coverage cert b) (binding-least binding b)

binding-policy-path : ∀ {S : Type₀} {A : S → Type₀}
  {X C : S → ℝ} {m} → MarginCertificate A X C m → BindingScenario A X C m →
  ∀ b → (m ≤ᵣ b) ≡ Coverage A X C b
binding-policy-path cert binding b = ua (binding-budget≃coverage cert binding b)
