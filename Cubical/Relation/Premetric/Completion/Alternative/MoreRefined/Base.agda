open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.Alternative.MoreRefined.Base
  {ℓ} {ℓ'} (M' : PremetricSpace ℓ ℓ') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat.Base as ℕ
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Base hiding (isProp∼)
open import Cubical.Data.Rationals.Order as ℚ
  renaming (_<_ to _<ℚ_ ; _≤_ to _≤ℚ_)
import Cubical.Data.Rationals.Properties as ℚ

open import Cubical.Relation.Binary.Properties

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ
open OrderedCommRingReasoning ℚOrderedCommRing
open OrderedCommRingTheory ℚOrderedCommRing

private
  M = M' .fst
  module PM = PremetricStr (M' .snd)


data ℭ̂ₛ : Type (ℓ-max ℓ ℓ')
data _∼̂ₛ[_]_ : ℭ̂ₛ → ℚ₊ → ℭ̂ₛ → Type (ℓ-max ℓ ℓ')

CauchySeq : (ℕ → ℭ̂ₛ) → Type (ℓ-max ℓ ℓ')
CauchySeq x =
  Σ[ μ ∈ (ℚ₊ → ℕ) ]
    (∀ ε m n → μ ε ℕ.≤ m → μ ε ℕ.≤ n →
      x m ∼̂ₛ[ ε ] x n)

SeqWitness : (ℕ → ℭ̂ₛ) → Type (ℓ-max ℓ ℓ')
SeqWitness x = ∥ CauchySeq x ∥₁


data ℭ̂ₛ where
  ι   : M → ℭ̂ₛ
  lim : (x : ℕ → ℭ̂ₛ) → SeqWitness x → ℭ̂ₛ
  eqℭ : ∀ x y → (∀ ε → x ∼̂ₛ[ ε ] y) → x ≡ y

data _∼̂ₛ[_]_ where
  ι-ι : ∀ x y ε → x PM.≈[ ε ] y → ι x ∼̂ₛ[ ε ] ι y

  ι-lim : ∀ x y μ ε δ yc Δ
    → ι x ∼̂ₛ[ ε -₊ δ , Δ ] y (μ δ)
    → ι x ∼̂ₛ[ ε ] lim y ∣ μ , yc ∣₁

  lim-ι : ∀ x μ y ε δ xc Δ
    → x (μ δ) ∼̂ₛ[ ε -₊ δ , Δ ] ι y
    → lim x ∣ μ , xc ∣₁ ∼̂ₛ[ ε ] ι y

  lim-lim : ∀ x μ y ν ε δ η xc yc Δ
    → x (μ δ) ∼̂ₛ[
        ε -₊ (δ +₊ η) , Δ
      ] y (ν η)
    → lim x ∣ μ , xc ∣₁ ∼̂ₛ[ ε ] lim y ∣ ν , yc ∣₁

  mono∼ : ∀ x y ε δ → ε <₊ δ →
    x ∼̂ₛ[ ε ] y → x ∼̂ₛ[ δ ] y

  sym∼ : ∀ x y ε → x ∼̂ₛ[ ε ] y → y ∼̂ₛ[ ε ] x

  tri∼ : ∀ x y z ε δ →
    x ∼̂ₛ[ ε ] y → y ∼̂ₛ[ δ ] z →
    x ∼̂ₛ[ ε +₊ δ ] z

  isProp∼ : ∀ x ε y → isProp (x ∼̂ₛ[ ε ] y)


isMonotone∼̂ₛ< : ∀ x y ε ε' → ε <₊ ε' →
  x ∼̂ₛ[ ε ] y → x ∼̂ₛ[ ε' ] y
isMonotone∼̂ₛ< x y ε ε' ε<ε' (ι-ι x' y' .ε x≈y) =
  ι-ι x' y' ε' (PM.isMonotone≈< x' y' ε ε' ε<ε' x≈y)
isMonotone∼̂ₛ< x y ε ε' ε<ε'
  (ι-lim x' y' μ .ε δ yc Δ r) =
  ι-lim x' y' μ ε' δ yc Δ'
    (isMonotone∼̂ₛ< _ _ _ _ inner< r)
  where
  δ<ε : δ <₊ ε
  δ<ε = 0<Δ→< (fst δ) (fst ε) Δ

  δ<ε' : δ <₊ ε'
  δ<ε' = begin< fst δ <⟨ δ<ε ⟩ fst ε <⟨ ε<ε' ⟩ fst ε' ◾

  Δ' : 0 ℚ.< ε' -₊ δ
  Δ' = <→0<Δ (fst δ) (fst ε') δ<ε'

  inner< : (ε -₊ δ , Δ) <₊ (ε' -₊ δ , Δ')
  inner< = OrderedCommRingStr.+MonoR< (snd ℚOrderedCommRing)
    (fst ε) (fst ε') (ℚ.- fst δ) ε<ε'
isMonotone∼̂ₛ< x y ε ε' ε<ε'
  (lim-ι x' μ y' .ε δ xc Δ r) =
  lim-ι x' μ y' ε' δ xc Δ'
    (isMonotone∼̂ₛ< _ _ _ _ inner< r)
  where
  δ<ε : δ <₊ ε
  δ<ε = 0<Δ→< (fst δ) (fst ε) Δ

  δ<ε' : δ <₊ ε'
  δ<ε' = begin< fst δ <⟨ δ<ε ⟩ fst ε <⟨ ε<ε' ⟩ fst ε' ◾

  Δ' : 0 ℚ.< ε' -₊ δ
  Δ' = <→0<Δ (fst δ) (fst ε') δ<ε'

  inner< : (ε -₊ δ , Δ) <₊ (ε' -₊ δ , Δ')
  inner< = OrderedCommRingStr.+MonoR< (snd ℚOrderedCommRing)
    (fst ε) (fst ε') (ℚ.- fst δ) ε<ε'
isMonotone∼̂ₛ< x y ε ε' ε<ε'
  (lim-lim x' μ y' ν .ε δ η xc yc Δ r) =
  lim-lim x' μ y' ν ε' δ η xc yc Δ'
    (isMonotone∼̂ₛ< _ _ _ _ inner< r)
  where
  ρ = δ +₊ η

  ρ<ε : ρ <₊ ε
  ρ<ε = 0<Δ→< (fst ρ) (fst ε) Δ

  ρ<ε' : ρ <₊ ε'
  ρ<ε' = begin< fst ρ <⟨ ρ<ε ⟩ fst ε <⟨ ε<ε' ⟩ fst ε' ◾

  Δ' : 0 ℚ.< ε' -₊ ρ
  Δ' = <→0<Δ (fst ρ) (fst ε') ρ<ε'

  inner< : (ε -₊ ρ , Δ) <₊ (ε' -₊ ρ , Δ')
  inner< = OrderedCommRingStr.+MonoR< (snd ℚOrderedCommRing)
    (fst ε) (fst ε') (ℚ.- fst ρ) ε<ε'
isMonotone∼̂ₛ< x y ε ε' ε<ε' (mono∼ x' y' δ .ε δ<ε r) =
  mono∼ x' y' δ ε'
    (ℚ.isTrans< _ _ _ δ<ε ε<ε') r
isMonotone∼̂ₛ< x y ε ε' ε<ε' (sym∼ x' y' .ε r) =
  sym∼ x' y' ε' (isMonotone∼̂ₛ< x' y' ε ε' ε<ε' r)
isMonotone∼̂ₛ< x y .(δ +₊ η) ε' sum<ε'
  (tri∼ x' z y' δ η r s) =
  mono∼ x' y' (δ +₊ η) ε' sum<ε'
    (tri∼ x' z y' δ η r s)
isMonotone∼̂ₛ< x y ε ε' ε<ε'
  (isProp∼ x' .ε y' p q i) =
  isProp∼ x' ε' y'
    (isMonotone∼̂ₛ< x' y' ε ε' ε<ε' p)
    (isMonotone∼̂ₛ< x' y' ε ε' ε<ε' q) i


isRefl∼̂ₛ : ∀ x ε → x ∼̂ₛ[ ε ] x
isRefl∼̂ₛ (ι x) ε = ι-ι x x ε (PM.isRefl≈ x ε)
isRefl∼̂ₛ (lim x gx) ε =
  PT.elim
    (λ gx → isProp∼ (lim x gx) ε (lim x gx))
    (λ { (μ , xc) → limit-refl x μ xc ε }) gx
  where
  limit-refl : ∀ x μ xc ε →
    lim x ∣ μ , xc ∣₁ ∼̂ₛ[ ε ] lim x ∣ μ , xc ∣₁
  limit-refl x μ xc ε =
    let δ = ε /4₊
        outer = δ +₊ δ
        outer<ε : outer <₊ ε
        outer<ε = begin<
          fst outer ≡→≤⟨ /4+/4≡/2 (fst ε) ⟩
          fst (ε /2₊) <⟨ /2₊<id ε ⟩
          fst ε ◾
        Δ = <→0<Δ (fst outer) (fst ε) outer<ε
    in lim-lim x μ x μ ε δ δ xc xc Δ
      (isRefl∼̂ₛ (x (μ δ)) (ε -₊ outer , Δ))
isRefl∼̂ₛ (eqℭ x y x∼y i) ε =
  isProp→PathP
    (λ j → isProp∼ (eqℭ x y x∼y j) ε (eqℭ x y x∼y j))
    (isRefl∼̂ₛ x ε) (isRefl∼̂ₛ y ε) i


isSetℭ̂ₛ : isSet ℭ̂ₛ
isSetℭ̂ₛ = reflPropRelImpliesIdentity→isSet
  (λ x y → ∀ ε → x ∼̂ₛ[ ε ] y)
  isRefl∼̂ₛ
  (λ x y → isPropΠ λ ε → isProp∼ x ε y)
  (eqℭ _ _)


record Elimℭ̂ₛ-Prop {ℓA} (A : ℭ̂ₛ → Type ℓA) :
  Type (ℓ-max ℓ (ℓ-max ℓ' ℓA)) where

  no-eta-equality

  field
    ιA      : ∀ x → A (ι x)
    limA    : ∀ x gx → (∀ n → A (x n)) → A (lim x gx)
    isPropA : ∀ x → isProp (A x)

  go : ∀ x → A x
  go (ι x) = ιA x
  go (lim x gx) = limA x gx (go ∘ x)
  go (eqℭ x y x∼y i) =
    isProp→PathP (λ j → isPropA (eqℭ x y x∼y j)) (go x) (go y) i


record Recℭ̂ₛ {ℓA ℓB} (A : Type ℓA)
  (B : A → A → ℚ₊ → Type ℓB) :
  Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓA ℓB))) where

  no-eta-equality

  field
    ιA : M → A
    limA : (x : ℕ → A)
      → ∥ Σ[ μ ∈ (ℚ₊ → ℕ) ]
          (∀ ε m n → μ ε ℕ.≤ m → μ ε ℕ.≤ n →
            B (x m) (x n) ε) ∥₁
      → A
    eqA : ∀ x y → (∀ ε → B x y ε) → x ≡ y

    ι-ι-B : ∀ x y ε → x PM.≈[ ε ] y → B (ιA x) (ιA y) ε
    ι-lim-B : ∀ x y μ ε δ yc Δ
      → B (ιA x) (y (μ δ)) (ε -₊ δ , Δ)
      → B (ιA x) (limA y ∣ μ , yc ∣₁) ε
    lim-ι-B : ∀ x μ y ε δ xc Δ
      → B (x (μ δ)) (ιA y) (ε -₊ δ , Δ)
      → B (limA x ∣ μ , xc ∣₁) (ιA y) ε
    lim-lim-B : ∀ x μ y ν ε δ η xc yc Δ
      → B (x (μ δ)) (y (ν η))
          (ε -₊ (δ +₊ η) , Δ)
      → B (limA x ∣ μ , xc ∣₁)
          (limA y ∣ ν , yc ∣₁) ε

    mono-B : ∀ x y ε δ → ε <₊ δ → B x y ε → B x y δ
    sym-B : ∀ x y ε → B x y ε → B y x ε
    tri-B : ∀ x y z ε δ →
      B x y ε → B y z δ → B x z (ε +₊ δ)

    isPropB : ∀ x y ε → isProp (B x y ε)

  go : ℭ̂ₛ → A
  go∼ : ∀ {x y ε} → x ∼̂ₛ[ ε ] y → B (go x) (go y) ε

  mapWitness : ∀ {x} → SeqWitness x →
    ∥ Σ[ μ ∈ (ℚ₊ → ℕ) ]
        (∀ ε m n → μ ε ℕ.≤ m → μ ε ℕ.≤ n →
          B (go (x m)) (go (x n)) ε) ∥₁
  mapWitness ∣ (μ , xc) ∣₁ =
    ∣ μ , (λ ε m n με≤m με≤n → go∼ (xc ε m n με≤m με≤n)) ∣₁
  mapWitness (squash₁ p q i) = squash₁ (mapWitness p) (mapWitness q) i

  go (ι x) = ιA x
  go (lim x gx) = limA (go ∘ x) (mapWitness gx)
  go (eqℭ x y x∼y i) =
    eqA (go x) (go y) (λ ε → go∼ (x∼y ε)) i

  go∼ (ι-ι x y ε x≈y) = ι-ι-B x y ε x≈y
  go∼ (ι-lim x y μ ε δ yc Δ r) =
    ι-lim-B x (go ∘ y) μ ε δ
      (λ θ m n μθ≤m μθ≤n → go∼ (yc θ m n μθ≤m μθ≤n))
      Δ (go∼ r)
  go∼ (lim-ι x μ y ε δ xc Δ r) =
    lim-ι-B (go ∘ x) μ y ε δ
      (λ θ m n μθ≤m μθ≤n → go∼ (xc θ m n μθ≤m μθ≤n))
      Δ (go∼ r)
  go∼ (lim-lim x μ y ν ε δ η xc yc Δ r) =
    lim-lim-B (go ∘ x) μ (go ∘ y) ν ε δ η
      (λ θ m n μθ≤m μθ≤n → go∼ (xc θ m n μθ≤m μθ≤n))
      (λ θ m n νθ≤m νθ≤n → go∼ (yc θ m n νθ≤m νθ≤n))
      Δ (go∼ r)
  go∼ (mono∼ x y ε δ ε<δ r) =
    mono-B (go x) (go y) ε δ ε<δ (go∼ r)
  go∼ (sym∼ x y ε r) = sym-B (go x) (go y) ε (go∼ r)
  go∼ (tri∼ x y z ε δ r s) =
    tri-B (go x) (go y) (go z) ε δ (go∼ r) (go∼ s)
  go∼ (isProp∼ x ε y p q i) =
    isProp→PathP
      (λ j → isPropB (go x) (go y) ε)
      (go∼ p) (go∼ q) i

  β-go-ι : ∀ x → go (ι x) ≡ ιA x
  β-go-ι _ = refl

  β-go-lim : ∀ x gx →
    go (lim x gx) ≡ limA (go ∘ x) (mapWitness gx)
  β-go-lim _ _ = refl
