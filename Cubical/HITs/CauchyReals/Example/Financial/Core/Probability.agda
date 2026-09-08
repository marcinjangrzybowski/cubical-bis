module Cubical.HITs.CauchyReals.Example.Financial.Core.Probability where

open import Cubical.HITs.CauchyReals.Example.Financial.Core.Finite public
open import Cubical.Data.Sigma using (_×_; Σ≡Prop)

-- Zero-probability scenarios are allowed. No division by a probability occurs.
ProbabilityLaws : ∀ {n} → Vector n → Type₀
ProbabilityLaws p = (∀ i → 0 ≤ᵣ p i) × (sum p ≡ 1)

isPropProbabilityLaws : ∀ {n} (p : Vector n) → isProp (ProbabilityLaws p)
isPropProbabilityLaws p =
  isProp× (isPropΠ (λ i → isProp≤ᵣ 0 (p i))) (isSetℝ _ _)

Distribution : ℕ → Type₀
Distribution n = Σ (Vector n) ProbabilityLaws

probability : ∀ {n} → Distribution n → Vector n
probability = fst

probability-nonnegative : ∀ {n} (P : Distribution n) i → 0 ≤ᵣ probability P i
probability-nonnegative P = fst (snd P)

probability-total : ∀ {n} (P : Distribution n) → sum (probability P) ≡ 1
probability-total P = snd (snd P)

distribution-path : ∀ {n} {P Q : Distribution n} →
  (∀ i → probability P i ≡ probability Q i) → P ≡ Q
distribution-path p = Σ≡Prop isPropProbabilityLaws (funExt p)

isSetDistribution : ∀ n → isSet (Distribution n)
isSetDistribution n = isSetΣ (isSetΠ (λ _ → isSetℝ))
  (λ p → isProp→isSet (isPropProbabilityLaws p))

expectation : ∀ {n} → Distribution n → Vector n → ℝ
expectation P = dot (probability P)

expectation-add : ∀ {n} (P : Distribution n) (X Y : Vector n) →
  expectation P (λ i → X i +ᵣ Y i) ≡ expectation P X +ᵣ expectation P Y
expectation-add P = dot-add (probability P)

expectation-scale : ∀ {n} (P : Distribution n) a (X : Vector n) →
  expectation P (λ i → a ·ᵣ X i) ≡ a ·ᵣ expectation P X
expectation-scale P = dot-scale (probability P)

expectation-constant : ∀ {n} (P : Distribution n) c →
  expectation P (λ _ → c) ≡ c
expectation-constant P c = dot-constant (probability P) c
  ∙ cong (c ·ᵣ_) (probability-total P) ∙ ·IdR c

expectation-monotone : ∀ {n} (P : Distribution n) (X Y : Vector n) →
  (∀ i → X i ≤ᵣ Y i) → expectation P X ≤ᵣ expectation P Y
expectation-monotone P X Y = dot-monotone (probability P) X Y
  (probability-nonnegative P)

expectation-nonnegative : ∀ {n} (P : Distribution n) (X : Vector n) →
  (∀ i → 0 ≤ᵣ X i) → 0 ≤ᵣ expectation P X
expectation-nonnegative P X = dot-nonnegative (probability P) X
  (probability-nonnegative P)

expectation-cash : ∀ {n} (P : Distribution n) (X : Vector n) c →
  expectation P (λ i → X i +ᵣ c) ≡ expectation P X +ᵣ c
expectation-cash P X c = expectation-add P X (λ _ → c)
  ∙ cong (expectation P X +ᵣ_) (expectation-constant P c)

expectation-bounds : ∀ {n} (P : Distribution n) (X : Vector n) a b →
  (∀ i → a ≤ᵣ X i) → (∀ i → X i ≤ᵣ b) →
  (a ≤ᵣ expectation P X) × (expectation P X ≤ᵣ b)
expectation-bounds P X a b lower upper =
  isTrans≡≤ᵣ _ _ _ (sym (expectation-constant P a))
    (expectation-monotone P (λ _ → a) X lower) ,
  isTrans≤≡ᵣ _ _ _ (expectation-monotone P X (λ _ → b) upper)
    (expectation-constant P b)

-- This estimate is useful for certified input approximations, even when the
-- underlying real comparison is undecidable.
expectation-perturbation : ∀ {n} (P : Distribution n) (X Y : Vector n) ε →
  (∀ i → X i ≤ᵣ Y i +ᵣ ε) → expectation P X ≤ᵣ expectation P Y +ᵣ ε
expectation-perturbation P X Y ε bound =
  isTrans≤≡ᵣ _ _ _ (expectation-monotone P X (λ i → Y i +ᵣ ε) bound)
    (expectation-cash P Y ε)

-- The order condition is an explicit density cap, rather than a Radon--Nikodym
-- derivative, so the definition remains meaningful at zero-probability atoms.
DensityCap : ∀ {n} → Distribution n → ℝ → Distribution n → Type₀
DensityCap P κ Q = ∀ i → probability Q i ≤ᵣ κ ·ᵣ probability P i

isPropDensityCap : ∀ {n} (P : Distribution n) κ Q → isProp (DensityCap P κ Q)
isPropDensityCap P κ Q = isPropΠ (λ _ → isProp≤ᵣ _ _)

capped-expectation : ∀ {n} (P Q : Distribution n) κ (X : Vector n) →
  DensityCap P κ Q → (∀ i → 0 ≤ᵣ X i) →
  expectation Q X ≤ᵣ κ ·ᵣ expectation P X
capped-expectation P Q κ X cap nonnegative =
  isTrans≤≡ᵣ _ _ _
    (sum-monotone (λ i → probability Q i ·ᵣ X i)
      (λ i → (κ ·ᵣ probability P i) ·ᵣ X i)
      (λ i → ≤ᵣ-·ᵣo _ _ (X i) (nonnegative i) (cap i)))
    (dot-left-scale κ (probability P) X)
