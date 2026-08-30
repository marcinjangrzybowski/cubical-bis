open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.Alternative.TruncatedScale
  {ℓ} {ℓ'} (M' : PremetricSpace ℓ ℓ') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Order as ℚ
  renaming (_<_ to _<ℚ_ ; _≤_ to _≤ℚ_)
import Cubical.Data.Rationals.Properties as ℚProp

open import Cubical.Relation.Binary.Properties

import Cubical.Relation.Premetric.Completion.Alternative
  as AlternativeDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Properties
  as AlternativePropertiesDefinition

module A = AlternativeDefinition M'
module AP = AlternativePropertiesDefinition M'

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ
open OrderedCommRingReasoning ℚOrderedCommRing
open OrderedCommRingTheory ℚOrderedCommRing

private
  M = M' .fst
  module PM = PremetricStr (M' .snd)


-- The scale and its Cauchy proof are stored only up to mere existence.

data ℭ̂ᵣ : Type (ℓ-max ℓ ℓ')
data _∼̂ᵣ[_]_ : ℭ̂ᵣ → ℚ₊ → ℭ̂ᵣ → Type (ℓ-max ℓ ℓ')

ScaleWitness : (ℚ₊ → ℭ̂ᵣ) → Type (ℓ-max ℓ ℓ')
ScaleWitness x =
  ∃[ g ∈ Γ ]
    (∀ ε δ → x ε ∼̂ᵣ[
      g .γ ε +₊ g .γ δ ] x δ)

data ℭ̂ᵣ where
  ι   : M → ℭ̂ᵣ
  lim : (x : ℚ₊ → ℭ̂ᵣ) → ScaleWitness x → ℭ̂ᵣ
  eqℭ : ∀ x y → (∀ ε → x ∼̂ᵣ[ ε ] y) → x ≡ y

data _∼̂ᵣ[_]_ where
  ι-ι : ∀ x y ε → x PM.≈[ ε ] y → ι x ∼̂ᵣ[ ε ] ι y

  ι-lim : ∀ x y g ε δ yc Δ
    → ι x ∼̂ᵣ[ ε -₊ g .γ δ , Δ ] y δ
    → ι x ∼̂ᵣ[ ε ] lim y ∣ g , yc ∣₁

  lim-ι : ∀ x g y ε δ xc Δ
    → x δ ∼̂ᵣ[ ε -₊ g .γ δ , Δ ] ι y
    → lim x ∣ g , xc ∣₁ ∼̂ᵣ[ ε ] ι y

  lim-lim : ∀ x g y g' ε δ η xc yc Δ
    → x δ ∼̂ᵣ[
        ε -₊ (g .γ δ +₊ g' .γ η) , Δ
      ] y η
    → lim x ∣ g , xc ∣₁ ∼̂ᵣ[ ε ] lim y ∣ g' , yc ∣₁

  isProp∼ : ∀ x ε y → isProp (x ∼̂ᵣ[ ε ] y)


isMonotone∼̂ᵣ< : ∀ x y ε ε' → ε <₊ ε' →
  x ∼̂ᵣ[ ε ] y → x ∼̂ᵣ[ ε' ] y
isMonotone∼̂ᵣ< x y ε ε' ε<ε' (ι-ι x' y' .ε x≈y) =
  ι-ι x' y' ε' (PM.isMonotone≈< x' y' ε ε' ε<ε' x≈y)
isMonotone∼̂ᵣ< x y ε ε' ε<ε'
  (ι-lim x' y' g .ε δ yc Δ r) =
  let ρ = g .γ δ
      ρ<ε : ρ <₊ ε
      ρ<ε = 0<Δ→< (fst ρ) (fst ε) Δ
      ρ<ε' : ρ <₊ ε'
      ρ<ε' = begin< fst ρ <⟨ ρ<ε ⟩ fst ε <⟨ ε<ε' ⟩ fst ε' ◾
      Δ' = <→0<Δ (fst ρ) (fst ε') ρ<ε'
      inner< : (ε -₊ ρ , Δ) <₊ (ε' -₊ ρ , Δ')
      inner< = OrderedCommRingStr.+MonoR< (snd ℚOrderedCommRing)
        (fst ε) (fst ε') (ℚProp.-_ (fst ρ)) ε<ε'
  in ι-lim x' y' g ε' δ yc Δ'
       (isMonotone∼̂ᵣ< _ _ _ _ inner< r)
isMonotone∼̂ᵣ< x y ε ε' ε<ε'
  (lim-ι x' g y' .ε δ xc Δ r) =
  let ρ = g .γ δ
      ρ<ε : ρ <₊ ε
      ρ<ε = 0<Δ→< (fst ρ) (fst ε) Δ
      ρ<ε' : ρ <₊ ε'
      ρ<ε' = begin< fst ρ <⟨ ρ<ε ⟩ fst ε <⟨ ε<ε' ⟩ fst ε' ◾
      Δ' = <→0<Δ (fst ρ) (fst ε') ρ<ε'
      inner< : (ε -₊ ρ , Δ) <₊ (ε' -₊ ρ , Δ')
      inner< = OrderedCommRingStr.+MonoR< (snd ℚOrderedCommRing)
        (fst ε) (fst ε') (ℚProp.-_ (fst ρ)) ε<ε'
  in lim-ι x' g y' ε' δ xc Δ'
       (isMonotone∼̂ᵣ< _ _ _ _ inner< r)
isMonotone∼̂ᵣ< x y ε ε' ε<ε'
  (lim-lim x' g y' g' .ε δ η xc yc Δ r) =
  let ρ = g .γ δ +₊ g' .γ η
      ρ<ε : ρ <₊ ε
      ρ<ε = 0<Δ→< (fst ρ) (fst ε) Δ
      ρ<ε' : ρ <₊ ε'
      ρ<ε' = begin< fst ρ <⟨ ρ<ε ⟩ fst ε <⟨ ε<ε' ⟩ fst ε' ◾
      Δ' = <→0<Δ (fst ρ) (fst ε') ρ<ε'
      inner< : (ε -₊ ρ , Δ) <₊ (ε' -₊ ρ , Δ')
      inner< = OrderedCommRingStr.+MonoR< (snd ℚOrderedCommRing)
        (fst ε) (fst ε') (ℚProp.-_ (fst ρ)) ε<ε'
  in lim-lim x' g y' g' ε' δ η xc yc Δ'
       (isMonotone∼̂ᵣ< _ _ _ _ inner< r)
isMonotone∼̂ᵣ< x y ε ε' ε<ε'
  (isProp∼ x' .ε y' p q i) =
  isProp∼ x' ε' y'
    (isMonotone∼̂ᵣ< x' y' ε ε' ε<ε' p)
    (isMonotone∼̂ᵣ< x' y' ε ε' ε<ε' q) i


isRefl∼̂ᵣ : ∀ x ε → x ∼̂ᵣ[ ε ] x
isRefl∼̂ᵣ (ι x) ε = ι-ι x x ε (PM.isRefl≈ x ε)
isRefl∼̂ᵣ (lim x gx) ε =
  PT.elim
    (λ gx → isProp∼ (lim x gx) ε (lim x gx))
    (λ { (g , xc) → limit-refl x g xc ε }) gx
  where
  limit-refl : ∀ x g xc ε →
    lim x ∣ g , xc ∣₁ ∼̂ᵣ[ ε ] lim x ∣ g , xc ∣₁
  limit-refl x g xc ε =
    let q = ε /4₊ /2₊
        δ = g .τ q
        ρ = g .γ δ
        inner = ρ +₊ ρ
        outer = ρ +₊ ρ
        ρ≤q = g .γ∘τ≤id q
        inner≤q+q : inner ≤₊ (q +₊ q)
        inner≤q+q = +Mono≤ _ _ _ _ ρ≤q ρ≤q
        total≤four-q : (inner +₊ outer) ≤₊ ((q +₊ q) +₊ (q +₊ q))
        total≤four-q = +Mono≤ _ _ _ _ inner≤q+q inner≤q+q
        four-q≡ε/2 : fst ((q +₊ q) +₊ (q +₊ q)) ≡ fst (ε /2₊)
        four-q≡ε/2 =
            cong (λ z → z ℚProp.+ z) (/2+/2≡id (fst (ε /4₊)))
          ∙ /4+/4≡/2 (fst ε)
        total<ε : fst (inner +₊ outer) <ℚ fst ε
        total<ε = begin<
          fst (inner +₊ outer) ≤⟨ total≤four-q ⟩
          fst ((q +₊ q) +₊ (q +₊ q)) ≡→≤⟨ four-q≡ε/2 ⟩
          fst (ε /2₊) <⟨ /2₊<id ε ⟩
          fst ε ◾
        outer<ε : outer <₊ ε
        outer<ε = begin<
          fst outer <⟨ <₊SumRight outer inner ⟩
          fst (inner +₊ outer) <⟨ total<ε ⟩
          fst ε ◾
        Δ = <→0<Δ (fst outer) (fst ε) outer<ε
        target = (ε -₊ outer , Δ)
        inner<target : inner <₊ target
        inner<target = +CancelR< (fst inner) (fst target) (fst outer)
          (subst (fst inner ℚProp.+ fst outer <ℚ_)
            (sym (minusPlus₊ ε outer)) total<ε)
        enlarged = isMonotone∼̂ᵣ< _ _ inner target inner<target (xc δ δ)
    in lim-lim x g x g ε δ δ xc xc Δ enlarged
isRefl∼̂ᵣ (eqℭ x y x∼y i) ε =
  isProp→PathP
    (λ j → isProp∼ (eqℭ x y x∼y j) ε (eqℭ x y x∼y j))
    (isRefl∼̂ᵣ x ε) (isRefl∼̂ᵣ y ε) i


isSetℭ̂ᵣ : isSet ℭ̂ᵣ
isSetℭ̂ᵣ = reflPropRelImpliesIdentity→isSet
  (λ x y → ∀ ε → x ∼̂ᵣ[ ε ] y)
  isRefl∼̂ᵣ
  (λ x y → isPropΠ λ ε → isProp∼ x ε y)
  (eqℭ _ _)

→ᵣ : A.ℭ̂ → ℭ̂ᵣ

∼→ᵣ : ∀ x y ε → x A.∼̂[ ε ] y → (→ᵣ x) ∼̂ᵣ[ ε ] (→ᵣ y) 

→ᵣ (A.ι x) = ι x
→ᵣ (A.lim x g x₁) = lim (λ ε → →ᵣ (x ε)) ∣ g , (λ ε δ → ∼→ᵣ _ _ _ (x₁ _ _)) ∣₁
→ᵣ (A.eqℭ x x₁ x₂ i) = eqℭ _ _ (λ ε → ∼→ᵣ _ _ _ ((x₂ ε)) ) i

∼→ᵣ x y ε (A.ι-ι x₁ y₁ ε₁ x₂) = ι-ι x₁ y₁ ε₁ x₂
∼→ᵣ x y ε (A.ι-lim x₁ y₁ g ε₁ δ yc Δ r) =
  ι-lim _ _ _ _ _ _ _ (∼→ᵣ _ _ _ r)
∼→ᵣ x y ε (A.lim-ι x₁ g y₁ ε₁ δ xc Δ r) =
  lim-ι _ _ _ _ _ _ _ (∼→ᵣ _ _ _ r)
∼→ᵣ x y ε (A.lim-lim x₁ g y₁ g' ε₁ δ η xc yc Δ r) =
  lim-lim _ _ _ _ _ _ _ _ _ _ (∼→ᵣ _ _ _ r)
∼→ᵣ x y ε (A.isProp∼ x₁ ε₁ y₁ x₂ x₃ i) =
 isProp∼ (→ᵣ x) ε (→ᵣ y) (∼→ᵣ x y ε x₂) (∼→ᵣ x y ε x₃) i

record Elimℭ̂ᵣ-Prop {ℓA} (A : ℭ̂ᵣ → Type ℓA) :
  Type (ℓ-max ℓ (ℓ-max ℓ' ℓA)) where

  no-eta-equality

  field
    ιA      : ∀ x → A (ι x)
    limA    : ∀ x gx → (∀ ε → A (x ε)) → A (lim x gx)
    isPropA : ∀ x → isProp (A x)

  go : ∀ x → A x
  go (ι x) = ιA x
  go (lim x gx) = limA x gx (go ∘ x)
  go (eqℭ x y x∼y i) =
    isProp→PathP (λ j → isPropA (eqℭ x y x∼y j)) (go x) (go y) i


record Recℭ̂ᵣ {ℓA ℓB} (A : Type ℓA)
  (B : A → A → ℚ₊ → Type ℓB) :
  Type (ℓ-max ℓ (ℓ-max ℓ' (ℓ-max ℓA ℓB))) where

  no-eta-equality

  field
    ιA : M → A
    limA : (x : ℚ₊ → A)
      → ∃[ g ∈ Γ ]
          (∀ ε δ → B (x ε) (x δ)
            (g .γ ε +₊ g .γ δ))
      → A
    eqA : ∀ x y → (∀ ε → B x y ε) → x ≡ y

    ι-ι-B : ∀ x y ε → x PM.≈[ ε ] y → B (ιA x) (ιA y) ε
    ι-lim-B : ∀ x y g ε δ yc Δ
      → B (ιA x) (y δ) (ε -₊ g .γ δ , Δ)
      → B (ιA x) (limA y ∣ g , yc ∣₁) ε
    lim-ι-B : ∀ x g y ε δ xc Δ
      → B (x δ) (ιA y) (ε -₊ g .γ δ , Δ)
      → B (limA x ∣ g , xc ∣₁) (ιA y) ε
    lim-lim-B : ∀ x g y g' ε δ η xc yc Δ
      → B (x δ) (y η)
          (ε -₊ (g .γ δ +₊ g' .γ η) , Δ)
      → B (limA x ∣ g , xc ∣₁) (limA y ∣ g' , yc ∣₁) ε

    isPropB : ∀ x y ε → isProp (B x y ε)

  go : ℭ̂ᵣ → A
  go∼ : ∀ {x y ε} → x ∼̂ᵣ[ ε ] y → B (go x) (go y) ε

  mapWitness : ∀ {x} → ScaleWitness x →
    ∃[ g ∈ Γ ]
      (∀ ε δ → B (go (x ε)) (go (x δ))
        (g .γ ε +₊ g .γ δ))
  mapWitness ∣ (g , xc) ∣₁ = ∣ g , (λ ε δ → go∼ (xc ε δ)) ∣₁
  mapWitness (squash₁ x x₁ i) = squash₁ (mapWitness x) (mapWitness x₁) i

  go (ι x) = ιA x
  go (lim x gx) = limA (λ ε → go (x ε)) (mapWitness gx)
  go (eqℭ x y x∼y i) =
    eqA (go x) (go y) (λ ε → go∼ (x∼y ε)) i

  go∼ (ι-ι x y ε x≈y) = ι-ι-B x y ε x≈y
  go∼ (ι-lim x y g ε δ yc Δ r) =
    ι-lim-B x (go ∘ y) g ε δ
      (λ θ κ → go∼ (yc θ κ)) Δ (go∼ r)
  go∼ (lim-ι x g y ε δ xc Δ r) =
    lim-ι-B (go ∘ x) g y ε δ
      (λ θ κ → go∼ (xc θ κ)) Δ (go∼ r)
  go∼ (lim-lim x g y g' ε δ η xc yc Δ r) =
    lim-lim-B (go ∘ x) g (λ ε → go (y ε)) g' ε δ η
      (λ θ κ → go∼ (xc θ κ))
      (λ θ κ → go∼ (yc θ κ)) Δ (go∼ r)
  go∼ (isProp∼ x ε y p q i) =
    isProp→PathP
      (λ j → isPropB (go x) (go y) ε)
      (go∼ p) (go∼ q) i

  β-go-ι : ∀ x → go (ι x) ≡ ιA x
  β-go-ι _ = refl

  β-go-lim : ∀ x gx →
    go (lim x gx) ≡ limA (go ∘ x) (mapWitness gx)
  β-go-lim _ _ = refl



private
  alternativeLimitRec : (x : ℚ₊ → A.ℭ̂) →
    PT.Rec→Set {A = Σ Γ λ v → (ε δ : ℚ₊) → x ε A.∼̂[ v .γ ε +₊ v .γ δ ] x δ} A.ℭ̂
  alternativeLimitRec x .PT.Rec→Set.isSetB = A.isSetℭ̂
  alternativeLimitRec x .PT.Rec→Set.f (g , xc) =
    A.lim x g xc
  alternativeLimitRec x .PT.Rec→Set.fconst (g , xc) (g' , xc') =
    AP.g-irrelevant x g g' xc xc'

  chooseAlternativeLimit : (x : ℚ₊ → A.ℭ̂)
    → ∃[ g ∈ Γ ]
        (∀ ε δ → x ε A.∼̂[
          g .γ ε +₊ g .γ δ ] x δ)
    → A.ℭ̂
  chooseAlternativeLimit x = PT.Rec→Set.go (alternativeLimitRec x)

  chooseAlternativeLimit-β : ∀ x g xc →
    chooseAlternativeLimit x ∣ g , xc ∣₁ ≡ A.lim x g xc
  chooseAlternativeLimit-β x g xc =
    PT.Rec→Set.β-go (alternativeLimitRec x) (g , xc)

  fromRec : Recℭ̂ᵣ A.ℭ̂
    (λ x y ε → x A.∼̂[ ε ] y)
  fromRec .Recℭ̂ᵣ.ιA = A.ι
  fromRec .Recℭ̂ᵣ.limA = chooseAlternativeLimit
  fromRec .Recℭ̂ᵣ.eqA = A.eqℭ
  fromRec .Recℭ̂ᵣ.ι-ι-B = A.ι-ι
  fromRec .Recℭ̂ᵣ.ι-lim-B = A.ι-lim
  fromRec .Recℭ̂ᵣ.lim-ι-B = A.lim-ι
  fromRec .Recℭ̂ᵣ.lim-lim-B = A.lim-lim
  fromRec .Recℭ̂ᵣ.isPropB x y ε = A.isProp∼ x ε y

toExplicitScale : ℭ̂ᵣ → A.ℭ̂
toExplicitScale = Recℭ̂ᵣ.go fromRec

toExplicitScale∼ : ∀ x y ε →
  x ∼̂ᵣ[ ε ] y →
  toExplicitScale x A.∼̂[ ε ] toExplicitScale y
toExplicitScale∼ x y ε = Recℭ̂ᵣ.go∼ fromRec


→ᵣ-ι : ∀ x → →ᵣ (A.ι x) ≡ ι x
→ᵣ-ι _ = refl

→ᵣ-lim : ∀ x g xc →
  →ᵣ (A.lim x g xc) ≡
    lim (→ᵣ ∘ x)
      ∣ g , (λ ε δ → ∼→ᵣ (x ε) (x δ) _ (xc ε δ)) ∣₁
→ᵣ-lim _ _ _ = refl

toExplicitScale-ι : ∀ x → toExplicitScale (ι x) ≡ A.ι x
toExplicitScale-ι = Recℭ̂ᵣ.β-go-ι fromRec

toExplicitScale-lim : ∀ x gx →
  toExplicitScale (lim x gx) ≡
    chooseAlternativeLimit (toExplicitScale ∘ x)
      (Recℭ̂ᵣ.mapWitness fromRec gx)
toExplicitScale-lim = Recℭ̂ᵣ.β-go-lim fromRec


private
  alternativeLimCong :
    ∀ (x y : ℚ₊ → A.ℭ̂) g
      (xc : ∀ ε δ → x ε A.∼̂[ g .γ ε +₊ g .γ δ ] x δ)
      (yc : ∀ ε δ → y ε A.∼̂[ g .γ ε +₊ g .γ δ ] y δ)
    → x ≡ y → A.lim x g xc ≡ A.lim y g yc
  alternativeLimCong x y g xc yc p =
    cong (λ z → A.lim (fst z) g (snd z)) pairPath
    where
    pairPath : (x , xc) ≡ (y , yc)
    pairPath = Σ≡Prop
      (λ z → isPropΠ2 λ ε δ →
        A.isProp∼ (z ε) (g .γ ε +₊ g .γ δ) (z δ)) p

  truncatedScaleLimCong :
    ∀ (x y : ℚ₊ → ℭ̂ᵣ) gx gy → x ≡ y →
      lim x gx ≡ lim y gy
  truncatedScaleLimCong x y gx gy p =
    cong (λ z → lim (fst z) (snd z)) pairPath
    where
    pairPath : (x , gx) ≡ (y , gy)
    pairPath = Σ≡Prop (λ _ → squash₁) p


toExplicitScale→ᵣ : ∀ x → toExplicitScale (→ᵣ x) ≡ x
toExplicitScale→ᵣ = A.Elimℭ̂-Prop.go e
  where
  e : A.Elimℭ̂-Prop (λ x → toExplicitScale (→ᵣ x) ≡ x)
  e .A.Elimℭ̂-Prop.ιA x =
    cong toExplicitScale (→ᵣ-ι x) ∙ toExplicitScale-ι x
  e .A.Elimℭ̂-Prop.limA x g xc IH =
      cong toExplicitScale (→ᵣ-lim x g xc)
    ∙ toExplicitScale-lim (→ᵣ ∘ x)
        ∣ g , (λ ε δ → ∼→ᵣ (x ε) (x δ) _ (xc ε δ)) ∣₁
    ∙ chooseAlternativeLimit-β _ g
        (λ ε δ → toExplicitScale∼ (→ᵣ (x ε)) (→ᵣ (x δ)) _
          (∼→ᵣ (x ε) (x δ) _ (xc ε δ)))
    ∙ alternativeLimCong _ _ g _ xc (funExt IH)
  e .A.Elimℭ̂-Prop.isPropA x = A.isSetℭ̂ _ _


→ᵣtoExplicitScale : ∀ x → →ᵣ (toExplicitScale x) ≡ x
→ᵣtoExplicitScale = Elimℭ̂ᵣ-Prop.go e
  where
  e : Elimℭ̂ᵣ-Prop (λ x → →ᵣ (toExplicitScale x) ≡ x)
  e .Elimℭ̂ᵣ-Prop.ιA x =
    cong →ᵣ (toExplicitScale-ι x) ∙ →ᵣ-ι x
  e .Elimℭ̂ᵣ-Prop.limA x gx IH =
    PT.elim
      (λ gx → isSetℭ̂ᵣ
        (→ᵣ (toExplicitScale (lim x gx))) (lim x gx))
      (λ { (g , xc) →
          cong →ᵣ (toExplicitScale-lim x ∣ g , xc ∣₁)
        ∙ cong →ᵣ
            (chooseAlternativeLimit-β (toExplicitScale ∘ x) g
              (λ ε δ → toExplicitScale∼ (x ε) (x δ) _ (xc ε δ)))
        ∙ →ᵣ-lim (toExplicitScale ∘ x) g
            (λ ε δ → toExplicitScale∼ (x ε) (x δ) _ (xc ε δ))
        ∙ truncatedScaleLimCong _ _ _ _ (funExt IH) }) gx
  e .Elimℭ̂ᵣ-Prop.isPropA x = isSetℭ̂ᵣ _ _


explicitTruncatedScaleIso : Iso A.ℭ̂ ℭ̂ᵣ
explicitTruncatedScaleIso .Iso.fun = →ᵣ
explicitTruncatedScaleIso .Iso.inv = toExplicitScale
explicitTruncatedScaleIso .Iso.sec = →ᵣtoExplicitScale
explicitTruncatedScaleIso .Iso.ret = toExplicitScale→ᵣ

explicitTruncatedScaleEquiv : A.ℭ̂ ≃ ℭ̂ᵣ
explicitTruncatedScaleEquiv = isoToEquiv explicitTruncatedScaleIso
