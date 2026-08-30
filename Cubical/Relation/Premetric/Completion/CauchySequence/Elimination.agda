open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.CauchySequence.Elimination
  {ℓ} {ℓ'} (M' : PremetricSpace ℓ ℓ') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat.Base as ℕ
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

import Cubical.Relation.Premetric.Completion.CauchySequence.Base
  as CauchyCompletion

module S = CauchyCompletion M'

open PositiveRationals

private
  M = M' .fst
  module PM = PremetricStr (M' .snd)


-- A radiuswise-truncated sequence witness whose closeness proofs have also
-- been decorated by a dependent motive.

ElimIsCauchySequence : ∀ {ℓA ℓB}
  (A : S.Completion → Type ℓA)
  (B : ∀ {x y : S.Completion} → A x → A y →
    ∀ ε → x S.≈ᶜ[ ε ] y → Type ℓB)
  {x : ℕ → S.Completion} (a∘x : ∀ n → A (x n)) →
  Type (ℓ-max ℓ (ℓ-max ℓ' ℓB))
ElimIsCauchySequence A B {x} a∘x = ∀ ε →
  ∥ Σ[ N ∈ ℕ ]
      (∀ m n → N ℕ.≤ m → N ℕ.≤ n →
        Σ[ r ∈ x m S.≈ᶜ[ ε ] x n ]
          B (a∘x m) (a∘x n) ε r) ∥₁


record ElimCompletion {ℓA ℓB} (A : S.Completion → Type ℓA)
  (B : ∀ {x y : S.Completion} → A x → A y →
    ∀ ε → x S.≈ᶜ[ ε ] y → Type ℓB) :
  Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓA ℓB))) where

  no-eta-equality

  field
    ιA : ∀ x → A (S.ι x)
    limA : ∀ x gx (a∘x : ∀ n → A (x n)) →
      ElimIsCauchySequence A B a∘x → A (S.lim x gx)
    eqA : ∀ {x y} p a a' →
      (∀ ε δ → B a a' (ε +₊ δ) (p (ε +₊ δ))) →
      (∀ ε → B a a' ε (p ε)) →
      PathP (λ i → A (S.eqCompletion x y p i)) a a'

    ι-ι-B : ∀ x y ε x≈y →
      B (ιA x) (ιA y) ε (S.ι-ι x y ε x≈y)
    ι-lim-B : ∀ x y gy N ε δ yc Δ r
      (a∘y : ∀ n → A (y n))
      (gyB : ElimIsCauchySequence A B a∘y)
      (ydc : ∀ m n (N≤m : N ℕ.≤ m) (N≤n : N ℕ.≤ n) →
        B (a∘y m) (a∘y n) δ
          (yc m n N≤m N≤n)) →
      B (ιA x) (a∘y N) (ε -₊ δ , Δ) r →
      B (ιA x) (limA y gy a∘y gyB) ε
        (S.ι-lim x y gy N ε δ yc Δ r)
    lim-ι-B : ∀ x gx N y ε δ xc Δ r
      (a∘x : ∀ n → A (x n))
      (gxB : ElimIsCauchySequence A B a∘x)
      (xdc : ∀ m n (N≤m : N ℕ.≤ m) (N≤n : N ℕ.≤ n) →
        B (a∘x m) (a∘x n) δ
          (xc m n N≤m N≤n)) →
      B (a∘x N) (ιA y) (ε -₊ δ , Δ) r →
      B (limA x gx a∘x gxB) (ιA y) ε
        (S.lim-ι x gx N y ε δ xc Δ r)
    lim-lim-B : ∀ x gx N y gy K ε δ η xc yc Δ r
      (a∘x : ∀ n → A (x n))
      (gxB : ElimIsCauchySequence A B a∘x)
      (xdc : ∀ m n (N≤m : N ℕ.≤ m) (N≤n : N ℕ.≤ n) →
        B (a∘x m) (a∘x n) δ
          (xc m n N≤m N≤n))
      (a∘y : ∀ n → A (y n))
      (gyB : ElimIsCauchySequence A B a∘y)
      (ydc : ∀ m n (K≤m : K ℕ.≤ m) (K≤n : K ℕ.≤ n) →
        B (a∘y m) (a∘y n) η
          (yc m n K≤m K≤n)) →
      B (a∘x N) (a∘y K) (ε -₊ (δ +₊ η) , Δ) r →
      B (limA x gx a∘x gxB) (limA y gy a∘y gyB) ε
        (S.lim-lim x gx N y gy K ε δ η xc yc Δ r)
    isPropB : ∀ {x y} a a' ε u →
      isProp (B {x} {y} a a' ε u)

  go : ∀ x → A x
  go≈ᶜ : ∀ {x y ε} (r : x S.≈ᶜ[ ε ] y) →
    B (go x) (go y) ε r

  mapWitness : ∀ {x} (gx : S.IsCauchySequence x) →
    ElimIsCauchySequence A B (go ∘ x)
  mapWitness {x} gx ε = mapAt (gx ε)
    where
    mapAt : ∥ S.CauchyTail x ε ∥₁ →
      ∥ Σ[ N ∈ ℕ ]
          (∀ m n → N ℕ.≤ m → N ℕ.≤ n →
            Σ[ r ∈ x m S.≈ᶜ[ ε ] x n ]
              B (go (x m)) (go (x n)) ε r) ∥₁
    mapAt ∣ N , xc ∣₁ =
      ∣ N , (λ m n N≤m N≤n →
        xc m n N≤m N≤n , go≈ᶜ (xc m n N≤m N≤n)) ∣₁
    mapAt (squash₁ p q i) = squash₁ (mapAt p) (mapAt q) i

  go (S.ι x) = ιA x
  go (S.lim x gx) = limA x gx (go ∘ x) (mapWitness gx)
  go (S.eqCompletion x y x∼y i) =
    eqA x∼y (go x) (go y)
      (λ ε δ → go≈ᶜ (x∼y (ε +₊ δ)))
      (λ ε → go≈ᶜ (x∼y ε)) i

  go≈ᶜ (S.ι-ι x y ε x≈y) = ι-ι-B x y ε x≈y
  go≈ᶜ (S.ι-lim x y gy N ε δ yc Δ r) =
    ι-lim-B x y gy N ε δ yc Δ r (go ∘ y) (mapWitness gy)
      (λ m n N≤m N≤n → go≈ᶜ (yc m n N≤m N≤n)) (go≈ᶜ r)
  go≈ᶜ (S.lim-ι x gx N y ε δ xc Δ r) =
    lim-ι-B x gx N y ε δ xc Δ r (go ∘ x) (mapWitness gx)
      (λ m n N≤m N≤n → go≈ᶜ (xc m n N≤m N≤n)) (go≈ᶜ r)
  go≈ᶜ (S.lim-lim x gx N y gy K ε δ η xc yc Δ r) =
    lim-lim-B x gx N y gy K ε δ η xc yc Δ r
      (go ∘ x) (mapWitness gx)
      (λ m n N≤m N≤n → go≈ᶜ (xc m n N≤m N≤n))
      (go ∘ y) (mapWitness gy)
      (λ m n K≤m K≤n → go≈ᶜ (yc m n K≤m K≤n))
      (go≈ᶜ r)
  go≈ᶜ (S.isProp≈ᶜ x ε y p q i) =
    isProp→PathP
      (λ j → isPropB (go x) (go y) ε (S.isProp≈ᶜ x ε y p q j))
      (go≈ᶜ p) (go≈ᶜ q) i

  β-go-ι : ∀ x → go (S.ι x) ≡ ιA x
  β-go-ι _ = refl

  β-go-lim : ∀ x gx →
    go (S.lim x gx) ≡ limA x gx (go ∘ x) (mapWitness gx)
  β-go-lim _ _ = refl


record ElimApproximation {ℓB}
  (B : ∀ x y ε → x S.≈ᶜ[ ε ] y → Type ℓB) :
  Type (ℓ-max ℓ (ℓ-max ℓ' ℓB)) where

  no-eta-equality

  field
    ι-ι-B : ∀ x y ε x≈y →
      B (S.ι x) (S.ι y) ε (S.ι-ι x y ε x≈y)
    ι-lim-B : ∀ x y gy N ε δ yc Δ r →
      B (S.ι x) (y N) (ε -₊ δ , Δ) r →
      B (S.ι x) (S.lim y gy) ε
        (S.ι-lim x y gy N ε δ yc Δ r)
    lim-ι-B : ∀ x gx N y ε δ xc Δ r →
      B (x N) (S.ι y) (ε -₊ δ , Δ) r →
      B (S.lim x gx) (S.ι y) ε
        (S.lim-ι x gx N y ε δ xc Δ r)
    lim-lim-B : ∀ x gx N y gy K ε δ η xc yc Δ r →
      B (x N) (y K) (ε -₊ (δ +₊ η) , Δ) r →
      B (S.lim x gx) (S.lim y gy) ε
        (S.lim-lim x gx N y gy K ε δ η xc yc Δ r)
    isPropB : ∀ x y ε u → isProp (B x y ε u)

  go≈ᶜ : ∀ {x y ε} (r : x S.≈ᶜ[ ε ] y) → B x y ε r
  go≈ᶜ (S.ι-ι x y ε x≈y) = ι-ι-B x y ε x≈y
  go≈ᶜ (S.ι-lim x y gy N ε δ yc Δ r) =
    ι-lim-B x y gy N ε δ yc Δ r (go≈ᶜ r)
  go≈ᶜ (S.lim-ι x gx N y ε δ xc Δ r) =
    lim-ι-B x gx N y ε δ xc Δ r (go≈ᶜ r)
  go≈ᶜ (S.lim-lim x gx N y gy K ε δ η xc yc Δ r) =
    lim-lim-B x gx N y gy K ε δ η xc yc Δ r (go≈ᶜ r)
  go≈ᶜ (S.isProp≈ᶜ x ε y p q i) =
    isProp→PathP
      (λ j → isPropB x y ε (S.isProp≈ᶜ x ε y p q j))
      (go≈ᶜ p) (go≈ᶜ q) i


record RecApproximation {ℓB}
  (B : S.Completion → S.Completion → ℚ₊ → Type ℓB) :
  Type (ℓ-max ℓ (ℓ-max ℓ' ℓB)) where

  no-eta-equality

  field
    ι-ι-B : ∀ x y ε → x PM.≈[ ε ] y → B (S.ι x) (S.ι y) ε
    ι-lim-B : ∀ x y gy N ε δ yc Δ →
      S.ι x S.≈ᶜ[ ε -₊ δ , Δ ] y N →
      B (S.ι x) (y N) (ε -₊ δ , Δ) →
      B (S.ι x) (S.lim y gy) ε
    lim-ι-B : ∀ x gx N y ε δ xc Δ →
      x N S.≈ᶜ[ ε -₊ δ , Δ ] S.ι y →
      B (x N) (S.ι y) (ε -₊ δ , Δ) →
      B (S.lim x gx) (S.ι y) ε
    lim-lim-B : ∀ x gx N y gy K ε δ η xc yc Δ →
      x N S.≈ᶜ[ ε -₊ (δ +₊ η) , Δ ] y K →
      B (x N) (y K) (ε -₊ (δ +₊ η) , Δ) →
      B (S.lim x gx) (S.lim y gy) ε
    isPropB : ∀ x y ε → isProp (B x y ε)

  go≈ᶜ : ∀ {x y ε} → x S.≈ᶜ[ ε ] y → B x y ε
  go≈ᶜ = ElimApproximation.go≈ᶜ e
    where
    e : ElimApproximation (λ x y ε _ → B x y ε)
    e .ElimApproximation.ι-ι-B = ι-ι-B
    e .ElimApproximation.ι-lim-B = ι-lim-B
    e .ElimApproximation.lim-ι-B = lim-ι-B
    e .ElimApproximation.lim-lim-B = lim-lim-B
    e .ElimApproximation.isPropB = λ x y ε _ → isPropB x y ε


record ElimCompletion-Prop2 {ℓA}
  (A : S.Completion → S.Completion → Type ℓA) :
  Type (ℓ-max ℓ (ℓ-max ℓ' ℓA)) where

  no-eta-equality

  field
    ι-ιA : ∀ x y → A (S.ι x) (S.ι y)
    ι-limA : ∀ x y gy → (∀ n → A (S.ι x) (y n)) →
      A (S.ι x) (S.lim y gy)
    lim-ιA : ∀ x gx y → (∀ n → A (x n) (S.ι y)) →
      A (S.lim x gx) (S.ι y)
    lim-limA : ∀ x gx y gy → (∀ m n → A (x m) (y n)) →
      A (S.lim x gx) (S.lim y gy)
    isPropA : ∀ x y → isProp (A x y)

  go : ∀ x y → A x y
  go = S.ElimCompletion-Prop.go e
    where
    e : S.ElimCompletion-Prop (λ x → ∀ y → A x y)
    e .S.ElimCompletion-Prop.ιA x = S.ElimCompletion-Prop.go e'
      where
      e' : S.ElimCompletion-Prop (A (S.ι x))
      e' .S.ElimCompletion-Prop.ιA = ι-ιA x
      e' .S.ElimCompletion-Prop.limA = ι-limA x
      e' .S.ElimCompletion-Prop.isPropA = isPropA (S.ι x)
    e .S.ElimCompletion-Prop.limA x gx a∘x = S.ElimCompletion-Prop.go e'
      where
      e' : S.ElimCompletion-Prop (A (S.lim x gx))
      e' .S.ElimCompletion-Prop.ιA y =
        lim-ιA x gx y (λ n → a∘x n (S.ι y))
      e' .S.ElimCompletion-Prop.limA y gy a∘y =
        lim-limA x gx y gy (λ m n → a∘x m (y n))
      e' .S.ElimCompletion-Prop.isPropA = isPropA (S.lim x gx)
    e .S.ElimCompletion-Prop.isPropA x = isPropΠ (isPropA x)


record ElimCompletion-Prop2Sym {ℓA}
  (A : S.Completion → S.Completion → Type ℓA) :
  Type (ℓ-max ℓ (ℓ-max ℓ' ℓA)) where

  no-eta-equality

  field
    ι-ιA : ∀ x y → A (S.ι x) (S.ι y)
    ι-limA : ∀ x y gy → (∀ n → A (S.ι x) (y n)) →
      A (S.ι x) (S.lim y gy)
    lim-limA : ∀ x gx y gy → (∀ m n → A (x m) (y n)) →
      A (S.lim x gx) (S.lim y gy)
    isSymA : ∀ x y → A x y → A y x
    isPropA : ∀ x y → isProp (A x y)

  go : ∀ x y → A x y
  go = ElimCompletion-Prop2.go e
    where
    e : ElimCompletion-Prop2 A
    e .ElimCompletion-Prop2.ι-ιA = ι-ιA
    e .ElimCompletion-Prop2.ι-limA = ι-limA
    e .ElimCompletion-Prop2.lim-ιA x gx y IH =
      isSymA (S.ι y) (S.lim x gx)
        (ι-limA y x gx (λ n → isSymA (x n) (S.ι y) (IH n)))
    e .ElimCompletion-Prop2.lim-limA = lim-limA
    e .ElimCompletion-Prop2.isPropA = isPropA


record RecCompletion {ℓA ℓB} (A : Type ℓA)
  (B : A → A → ℚ₊ → Type ℓB) :
  Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓA ℓB))) where

  no-eta-equality

  SeqB : (ℕ → A) → Type ℓB
  SeqB x = ∀ ε →
    ∥ Σ[ N ∈ ℕ ]
        (∀ m n → N ℕ.≤ m → N ℕ.≤ n →
          B (x m) (x n) ε) ∥₁

  field
    ιA : M → A
    limA : (x : ℕ → A) → SeqB x → A
    eqA : ∀ x y → (∀ ε → B x y ε) → x ≡ y

    ι-ι-B : ∀ x y ε → x PM.≈[ ε ] y → B (ιA x) (ιA y) ε
    ι-lim-B : ∀ x y gyB N ε δ
      (ycB : ∀ m n → N ℕ.≤ m → N ℕ.≤ n →
        B (y m) (y n) δ) Δ →
      B (ιA x) (y N) (ε -₊ δ , Δ) →
      B (ιA x) (limA y gyB) ε
    lim-ι-B : ∀ x gxB N y ε δ
      (xcB : ∀ m n → N ℕ.≤ m → N ℕ.≤ n →
        B (x m) (x n) δ) Δ →
      B (x N) (ιA y) (ε -₊ δ , Δ) →
      B (limA x gxB) (ιA y) ε
    lim-lim-B : ∀ x gxB N y gyB K ε δ η
      (xcB : ∀ m n → N ℕ.≤ m → N ℕ.≤ n →
        B (x m) (x n) δ)
      (ycB : ∀ m n → K ℕ.≤ m → K ℕ.≤ n →
        B (y m) (y n) η) Δ →
      B (x N) (y K) (ε -₊ (δ +₊ η) , Δ) →
      B (limA x gxB) (limA y gyB) ε

    isPropB : ∀ x y ε → isProp (B x y ε)

  go : S.Completion → A
  go≈ᶜ : ∀ {x y ε} → x S.≈ᶜ[ ε ] y → B (go x) (go y) ε

  mapWitness : ∀ {x} → S.IsCauchySequence x → SeqB (go ∘ x)
  mapWitness {x} gx ε = mapAt (gx ε)
    where
    mapAt : ∥ S.CauchyTail x ε ∥₁ →
      ∥ Σ[ N ∈ ℕ ]
          (∀ m n → N ℕ.≤ m → N ℕ.≤ n →
            B (go (x m)) (go (x n)) ε) ∥₁
    mapAt ∣ N , xc ∣₁ =
      ∣ N , (λ m n N≤m N≤n → go≈ᶜ (xc m n N≤m N≤n)) ∣₁
    mapAt (squash₁ p q i) = squash₁ (mapAt p) (mapAt q) i

  go (S.ι x) = ιA x
  go (S.lim x gx) = limA (go ∘ x) (mapWitness gx)
  go (S.eqCompletion x y x∼y i) =
    eqA (go x) (go y) (λ ε → go≈ᶜ (x∼y ε)) i

  go≈ᶜ (S.ι-ι x y ε x≈y) = ι-ι-B x y ε x≈y
  go≈ᶜ (S.ι-lim x y gy N ε δ yc Δ r) =
    ι-lim-B x (go ∘ y) (mapWitness gy) N ε δ
      (λ m n N≤m N≤n → go≈ᶜ (yc m n N≤m N≤n)) Δ (go≈ᶜ r)
  go≈ᶜ (S.lim-ι x gx N y ε δ xc Δ r) =
    lim-ι-B (go ∘ x) (mapWitness gx) N y ε δ
      (λ m n N≤m N≤n → go≈ᶜ (xc m n N≤m N≤n)) Δ (go≈ᶜ r)
  go≈ᶜ (S.lim-lim x gx N y gy K ε δ η xc yc Δ r) =
    lim-lim-B (go ∘ x) (mapWitness gx) N
      (go ∘ y) (mapWitness gy) K ε δ η
      (λ m n N≤m N≤n → go≈ᶜ (xc m n N≤m N≤n))
      (λ m n K≤m K≤n → go≈ᶜ (yc m n K≤m K≤n))
      Δ (go≈ᶜ r)
  go≈ᶜ (S.isProp≈ᶜ x ε y p q i) =
    isProp→PathP (λ _ → isPropB (go x) (go y) ε) (go≈ᶜ p) (go≈ᶜ q) i

  β-go-ι : ∀ x → go (S.ι x) ≡ ιA x
  β-go-ι _ = refl

  β-go-lim : ∀ x gx →
    go (S.lim x gx) ≡ limA (go ∘ x) (mapWitness gx)
  β-go-lim _ _ = refl


record RecCompletionSym {ℓA ℓB} (A : Type ℓA)
  (B : A → A → ℚ₊ → Type ℓB) :
  Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓA ℓB))) where

  no-eta-equality

  field
    ιA : M → A
    limA : (x : ℕ → A) →
      (∀ ε → ∥ Σ[ N ∈ ℕ ]
        (∀ m n → N ℕ.≤ m → N ℕ.≤ n →
          B (x m) (x n) ε) ∥₁) → A
    eqA : ∀ x y → (∀ ε → B x y ε) → x ≡ y

    ι-ι-B : ∀ x y ε → x PM.≈[ ε ] y → B (ιA x) (ιA y) ε
    ι-lim-B : ∀ x y gyB N ε δ
      (ycB : ∀ m n → N ℕ.≤ m → N ℕ.≤ n →
        B (y m) (y n) δ) Δ →
      B (ιA x) (y N) (ε -₊ δ , Δ) →
      B (ιA x) (limA y gyB) ε
    lim-lim-B : ∀ x gxB N y gyB K ε δ η
      (xcB : ∀ m n → N ℕ.≤ m → N ℕ.≤ n →
        B (x m) (x n) δ)
      (ycB : ∀ m n → K ℕ.≤ m → K ℕ.≤ n →
        B (y m) (y n) η) Δ →
      B (x N) (y K) (ε -₊ (δ +₊ η) , Δ) →
      B (limA x gxB) (limA y gyB) ε

    isSymB : ∀ x y ε → B x y ε → B y x ε
    isPropB : ∀ x y ε → isProp (B x y ε)

  private
    r : RecCompletion A B
    r .RecCompletion.ιA = ιA
    r .RecCompletion.limA = limA
    r .RecCompletion.eqA = eqA
    r .RecCompletion.ι-ι-B = ι-ι-B
    r .RecCompletion.ι-lim-B = ι-lim-B
    r .RecCompletion.lim-ι-B x gxB N y ε δ xcB Δ inner =
      isSymB (ιA y) (limA x gxB) ε
        (ι-lim-B y x gxB N ε δ
          (λ m n N≤m N≤n →
            isSymB (x n) (x m) δ (xcB n m N≤n N≤m))
          Δ (isSymB (x N) (ιA y) (ε -₊ δ , Δ) inner))
    r .RecCompletion.lim-lim-B = lim-lim-B
    r .RecCompletion.isPropB = isPropB

  go : S.Completion → A
  go = RecCompletion.go r

  go≈ᶜ : ∀ {x y ε} → x S.≈ᶜ[ ε ] y → B (go x) (go y) ε
  go≈ᶜ = RecCompletion.go≈ᶜ r
