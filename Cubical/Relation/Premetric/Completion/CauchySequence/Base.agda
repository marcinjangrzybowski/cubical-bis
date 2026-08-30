open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.CauchySequence.Base
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


-- The choice of a tail is truncated separately at each radius.  Thus this
-- condition contains no simultaneous choice of a modulus ℚ₊ → ℕ.

data Completion : Type (ℓ-max ℓ ℓ')
data _≈ᶜ[_]_ : Completion → ℚ₊ → Completion → Type (ℓ-max ℓ ℓ')

CauchyTail : (ℕ → Completion) → ℚ₊ → Type (ℓ-max ℓ ℓ')
CauchyTail x ε =
  Σ[ N ∈ ℕ ]
    (∀ m n → N ℕ.≤ m → N ℕ.≤ n →
      x m ≈ᶜ[ ε ] x n)

IsCauchySequence : (ℕ → Completion) → Type (ℓ-max ℓ ℓ')
IsCauchySequence x = ∀ ε → ∥ CauchyTail x ε ∥₁

isPropIsCauchySequence : ∀ x → isProp (IsCauchySequence x)
isPropIsCauchySequence x = isPropΠ λ _ → squash₁


data Completion where
  ι   : M → Completion
  lim : (x : ℕ → Completion) → IsCauchySequence x → Completion
  eqCompletion : ∀ x y → (∀ ε → x ≈ᶜ[ ε ] y) → x ≡ y

data _≈ᶜ[_]_ where
  ι-ι : ∀ x y ε → x PM.≈[ ε ] y → ι x ≈ᶜ[ ε ] ι y

  ι-lim : ∀ x y (gy : IsCauchySequence y) N ε δ
    (yc : ∀ m n → N ℕ.≤ m → N ℕ.≤ n →
      y m ≈ᶜ[ δ ] y n)
    Δ →
    ι x ≈ᶜ[ ε -₊ δ , Δ ] y N →
    ι x ≈ᶜ[ ε ] lim y gy

  lim-ι : ∀ x (gx : IsCauchySequence x) N y ε δ
    (xc : ∀ m n → N ℕ.≤ m → N ℕ.≤ n →
      x m ≈ᶜ[ δ ] x n)
    Δ →
    x N ≈ᶜ[ ε -₊ δ , Δ ] ι y →
    lim x gx ≈ᶜ[ ε ] ι y

  lim-lim : ∀ x (gx : IsCauchySequence x) N y (gy : IsCauchySequence y) K ε δ η
    (xc : ∀ m n → N ℕ.≤ m → N ℕ.≤ n →
      x m ≈ᶜ[ δ ] x n)
    (yc : ∀ m n → K ℕ.≤ m → K ℕ.≤ n →
      y m ≈ᶜ[ η ] y n)
    Δ →
    x N ≈ᶜ[ ε -₊ (δ +₊ η) , Δ ] y K →
    lim x gx ≈ᶜ[ ε ] lim y gy

  isProp≈ᶜ : ∀ x ε y → isProp (x ≈ᶜ[ ε ] y)


isMonotone≈ᶜ< : ∀ x y ε ε' → ε <₊ ε' →
  x ≈ᶜ[ ε ] y → x ≈ᶜ[ ε' ] y
isMonotone≈ᶜ< x y ε ε' ε<ε' (ι-ι x' y' .ε x≈y) =
  ι-ι x' y' ε' (PM.isMonotone≈< x' y' ε ε' ε<ε' x≈y)
isMonotone≈ᶜ< x y ε ε' ε<ε'
  (ι-lim x' y' gy N .ε δ yc Δ r) =
  ι-lim x' y' gy N ε' δ yc Δ'
    (isMonotone≈ᶜ< _ _ _ _ inner< r)
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
isMonotone≈ᶜ< x y ε ε' ε<ε'
  (lim-ι x' gx N y' .ε δ xc Δ r) =
  lim-ι x' gx N y' ε' δ xc Δ'
    (isMonotone≈ᶜ< _ _ _ _ inner< r)
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
isMonotone≈ᶜ< x y ε ε' ε<ε'
  (lim-lim x' gx N y' gy K .ε δ η xc yc Δ r) =
  lim-lim x' gx N y' gy K ε' δ η xc yc Δ'
    (isMonotone≈ᶜ< _ _ _ _ inner< r)
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
isMonotone≈ᶜ< x y ε ε' ε<ε'
  (isProp≈ᶜ x' .ε y' p q i) =
  isProp≈ᶜ x' ε' y'
    (isMonotone≈ᶜ< x' y' ε ε' ε<ε' p)
    (isMonotone≈ᶜ< x' y' ε ε' ε<ε' q) i


sym≈ᶜ : ∀ x y ε → x ≈ᶜ[ ε ] y → y ≈ᶜ[ ε ] x
sym≈ᶜ .(ι x) .(ι y) ε (ι-ι x y .ε x≈y) =
  ι-ι y x ε (PM.isSym≈ x y ε x≈y)
sym≈ᶜ .(ι x) .(lim y gy) ε
  (ι-lim x y gy N .ε δ yc Δ inner) =
  lim-ι y gy N x ε δ yc Δ (sym≈ᶜ _ _ _ inner)
sym≈ᶜ .(lim x gx) .(ι y) ε
  (lim-ι x gx N y .ε δ xc Δ inner) =
  ι-lim y x gx N ε δ xc Δ (sym≈ᶜ _ _ _ inner)
sym≈ᶜ .(lim x gx) .(lim y gy) ε
  (lim-lim x gx N y gy K .ε δ η xc yc Δ inner) =
  lim-lim y gy K x gx N ε η δ yc xc Δ' inner'
  where
  radius≡ : ε -₊ (δ +₊ η) ≡ ε -₊ (η +₊ δ)
  radius≡ = cong (λ z → fst ε ℚ.- z) (ℚ.+Comm (fst δ) (fst η))

  Δ' : 0 ℚ.< ε -₊ (η +₊ δ)
  Δ' = subst (0 ℚ.<_) radius≡ Δ

  inner' : y K ≈ᶜ[ ε -₊ (η +₊ δ) , Δ' ] x N
  inner' = subst (y K ≈ᶜ[_] x N)
    (ℚ₊≡ radius≡) (sym≈ᶜ _ _ _ inner)
sym≈ᶜ x y ε (isProp≈ᶜ .x .ε .y p q i) =
  isProp≈ᶜ y ε x (sym≈ᶜ x y ε p) (sym≈ᶜ x y ε q) i


isRefl≈ᶜ : ∀ x ε → x ≈ᶜ[ ε ] x
isRefl≈ᶜ (ι x) ε = ι-ι x x ε (PM.isRefl≈ x ε)
isRefl≈ᶜ (lim x gx) ε =
  PT.rec (isProp≈ᶜ (lim x gx) ε (lim x gx)) withTail (gx δ)
  where
  δ = ε /4₊
  outer = δ +₊ δ

  outer<ε : outer <₊ ε
  outer<ε = begin<
    fst outer ≡→≤⟨ /4+/4≡/2 (fst ε) ⟩
    fst (ε /2₊) <⟨ /2₊<id ε ⟩
    fst ε ◾

  Δ : 0 ℚ.< ε -₊ outer
  Δ = <→0<Δ (fst outer) (fst ε) outer<ε

  withTail : CauchyTail x δ →
    lim x gx ≈ᶜ[ ε ] lim x gx
  withTail (N , xc) =
    lim-lim x gx N x gx N ε δ δ xc xc Δ
      (isRefl≈ᶜ (x N) (ε -₊ outer , Δ))
isRefl≈ᶜ (eqCompletion x y x∼y i) ε =
  isProp→PathP
    (λ j → isProp≈ᶜ (eqCompletion x y x∼y j) ε (eqCompletion x y x∼y j))
    (isRefl≈ᶜ x ε) (isRefl≈ᶜ y ε) i


isSetCompletion : isSet Completion
isSetCompletion = reflPropRelImpliesIdentity→isSet
  (λ x y → ∀ ε → x ≈ᶜ[ ε ] y)
  isRefl≈ᶜ
  (λ x y → isPropΠ λ ε → isProp≈ᶜ x ε y)
  (eqCompletion _ _)


record ElimCompletion-Prop {ℓA} (A : Completion → Type ℓA) :
  Type (ℓ-max ℓ (ℓ-max ℓ' ℓA)) where

  no-eta-equality

  field
    ιA      : ∀ x → A (ι x)
    limA    : ∀ x gx → (∀ n → A (x n)) → A (lim x gx)
    isPropA : ∀ x → isProp (A x)

  go : ∀ x → A x
  go (ι x) = ιA x
  go (lim x gx) = limA x gx (go ∘ x)
  go (eqCompletion x y x∼y i) =
    isProp→PathP (λ j → isPropA (eqCompletion x y x∼y j)) (go x) (go y) i
