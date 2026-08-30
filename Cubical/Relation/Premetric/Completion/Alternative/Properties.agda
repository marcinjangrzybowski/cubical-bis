open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.Alternative.Properties
  {ℓ} {ℓ'} (M' : PremetricSpace ℓ ℓ') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.Data.Rationals.Order as ℚ
  renaming (_<_ to _<ℚ_ ; _≤_ to _≤ℚ_)
import Cubical.Data.Rationals.Properties as ℚProp

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ
open OrderedCommRingReasoning ℚOrderedCommRing
open OrderedCommRingTheory ℚOrderedCommRing

open import Cubical.Relation.Premetric.Completion.Alternative M'
open import Cubical.Relation.Premetric.Completion.Base M'
  renaming (ℭ to ℭM ; _∼[_]_ to _∼ᵣ[_]_)

open Γ


-- Both maps preserve and reflect closeness.  This is stronger than merely
-- knowing that their underlying functions form an isomorphism.

←̂-reflects∼ : ∀ x y ε → ←̂ x ∼ᵣ[ ε ] ←̂ y → x ∼̂[ ε ] y
←̂-reflects∼ x y ε p =
  subst2 (λ u v → u ∼̂[ ε ] v) (→̂←̂ x) (→̂←̂ y) (→̂~ _ _ _ p)

→̂-reflects∼ : ∀ x y ε → →̂ x ∼̂[ ε ] →̂ y → x ∼ᵣ[ ε ] y
→̂-reflects∼ x y ε p =
  subst2 (λ u v → u ∼ᵣ[ ε ] v) (←̂→̂ x) (←̂→̂ y) (←̂~ _ _ _ p)

←̂-closenessEquiv : ∀ x y ε →
  (x ∼̂[ ε ] y) ≃ (←̂ x ∼ᵣ[ ε ] ←̂ y)
←̂-closenessEquiv x y ε = propBiimpl→Equiv
  (isProp∼ x ε y)
  (RegularPremetric.isProp≈ (←̂ x) (←̂ y) ε)
  (←̂~ x y ε)
  (←̂-reflects∼ x y ε)

→̂-closenessEquiv : ∀ x y ε →
  (x ∼ᵣ[ ε ] y) ≃ (→̂ x ∼̂[ ε ] →̂ y)
→̂-closenessEquiv x y ε = propBiimpl→Equiv
  (RegularPremetric.isProp≈ x y ε)
  (isProp∼ (→̂ x) ε (→̂ y))
  (→̂~ x y ε)
  (→̂-reflects∼ x y ε)


-- The remaining premetric laws can now be transferred through ←̂.

isMonotone∼̂≤ : ∀ x y ε δ → ε ≤₊ δ → x ∼̂[ ε ] y → x ∼̂[ δ ] y
isMonotone∼̂≤ x y ε δ ε≤δ p = ←̂-reflects∼ x y δ
  (RegularPremetric.isMonotone≈≤ _ _ ε δ ε≤δ (←̂~ x y ε p))

isSym∼̂ : ∀ x y ε → x ∼̂[ ε ] y → y ∼̂[ ε ] x
isSym∼̂ x y ε p = ←̂-reflects∼ y x ε
  (RegularPremetric.isSym≈ _ _ ε (←̂~ x y ε p))

isTriangular∼̂ : ∀ x y z ε δ →
  x ∼̂[ ε ] y → y ∼̂[ δ ] z → x ∼̂[ ε +₊ δ ] z
isTriangular∼̂ x y z ε δ p q = ←̂-reflects∼ x z (ε +₊ δ)
  (RegularPremetric.isTriangular≈ _ _ _ ε δ
    (←̂~ x y ε p) (←̂~ y z δ q))

isRounded∼̂ : ∀ x y ε →
  x ∼̂[ ε ] y → ∃[ δ ∈ ℚ₊ ] (δ <₊ ε) × (x ∼̂[ δ ] y)
isRounded∼̂ x y ε p = PT.map
  (λ (δ , δ<ε , q) → δ , δ<ε , ←̂-reflects∼ x y δ q)
  (RegularPremetric.isRounded≈ _ _ ε (←̂~ x y ε p))


ℭ̂IsPremetric : IsPremetric _∼̂[_]_
IsPremetric.isSetM ℭ̂IsPremetric = isSetℭ̂
IsPremetric.isProp≈ ℭ̂IsPremetric x y ε = isProp∼ x ε y
IsPremetric.isRefl≈ ℭ̂IsPremetric = isRefl∼̂
IsPremetric.isSym≈ ℭ̂IsPremetric = isSym∼̂
IsPremetric.isSeparated≈ ℭ̂IsPremetric = eqℭ
IsPremetric.isTriangular≈ ℭ̂IsPremetric = isTriangular∼̂
IsPremetric.isRounded≈ ℭ̂IsPremetric = isRounded∼̂

ℭ̂PremetricSpace :
  PremetricSpace (ℓ-max ℓ ℓ') (ℓ-max ℓ ℓ')
ℭ̂PremetricSpace .fst = ℭ̂
PremetricStr._≈[_]_ (ℭ̂PremetricSpace .snd) = _∼̂[_]_
PremetricStr.isPremetric (ℭ̂PremetricSpace .snd) = ℭ̂IsPremetric


-- The equality proof only needs a common index on which both scales are
-- small.  Strict monotonicity is one sufficient way to choose such an index,
-- but is stronger than the actual requirement.

JointSmallSelector : Γ → Γ → Type
JointSmallSelector g g' = ∀ q →
  Σ[ ζ ∈ ℚ₊ ] (g .γ ζ ≤₊ q) × (g' .γ ζ ≤₊ q)

monotoneJointSmallSelector : ∀ g g' → JointSmallSelector g g'
monotoneJointSmallSelector g g' q = ζ , c≤q , d≤q
  where
  δ = g .τ q
  η = g' .τ q
  ζ = min₊ δ η /2₊

  c<q : g .γ ζ <₊ q
  c<q = begin<
    fst (g .γ ζ) <⟨ g .mon-γ ζ δ (min/2₊<L δ η) ⟩
    fst (g .γ δ) ≤⟨ g .γ∘τ≤id q ⟩
    fst q ◾

  d<q : g' .γ ζ <₊ q
  d<q = begin<
    fst (g' .γ ζ) <⟨ g' .mon-γ ζ η (min/2₊<R δ η) ⟩
    fst (g' .γ η) ≤⟨ g' .γ∘τ≤id q ⟩
    fst q ◾

  c≤q : g .γ ζ ≤₊ q
  c≤q = OrderedCommRingStr.<-≤-weaken (snd ℚOrderedCommRing) _ _ c<q

  d≤q : g' .γ ζ ≤₊ q
  d≤q = OrderedCommRingStr.<-≤-weaken (snd ℚOrderedCommRing) _ _ d<q


g-irrelevant-with : ∀ x g g' cx cx' → JointSmallSelector g g'
  → lim x g cx ≡ lim x g' cx'
g-irrelevant-with x g g' cx cx' jointly-small = eqℭ _ _ λ ε →
  let q = ε /4₊ /4₊
      δ = g .τ q
      η = g' .τ q
      common = jointly-small q
      ζ = common .fst

      a = g .γ δ
      b = g' .γ η
      c = g .γ ζ
      d = g' .γ ζ

      a≤q : a ≤₊ q
      a≤q = g .γ∘τ≤id q
      b≤q : b ≤₊ q
      b≤q = g' .γ∘τ≤id q
      c≤q : c ≤₊ q
      c≤q = common .snd .fst
      d≤q : d ≤₊ q
      d≤q = common .snd .snd

      inner = (a +₊ c) +₊ (d +₊ b)
      outer = a +₊ b
      two-q = q +₊ q
      four-q = two-q +₊ two-q
      six-q = four-q +₊ two-q
      eight-q = four-q +₊ four-q

      a+c≤two-q : (a +₊ c) ≤₊ two-q
      a+c≤two-q = +Mono≤ _ _ _ _ a≤q c≤q
      d+b≤two-q : (d +₊ b) ≤₊ two-q
      d+b≤two-q = +Mono≤ _ _ _ _ d≤q b≤q
      inner≤four-q : inner ≤₊ four-q
      inner≤four-q = +Mono≤ _ _ _ _ a+c≤two-q d+b≤two-q
      outer≤two-q : outer ≤₊ two-q
      outer≤two-q = +Mono≤ _ _ _ _ a≤q b≤q
      total≤six-q : (inner +₊ outer) ≤₊ six-q
      total≤six-q = +Mono≤ _ _ _ _ inner≤four-q outer≤two-q
      two-q<four-q : two-q <₊ four-q
      two-q<four-q = <₊SumLeft two-q two-q
      six-q<eight-q : six-q <₊ eight-q
      six-q<eight-q = +MonoL<
        (fst two-q) (fst four-q) (fst four-q) two-q<four-q

      four-q≡ε/4 : fst four-q ≡ fst (ε /4₊)
      four-q≡ε/4 = /4+/4+/4+/4≡id (fst (ε /4₊))
      eight-q≡ε/2 : fst eight-q ≡ fst (ε /2₊)
      eight-q≡ε/2 =
          cong (λ z → z ℚProp.+ z) four-q≡ε/4
        ∙ /4+/4≡/2 (fst ε)
      total<ε : fst (inner +₊ outer) <ℚ fst ε
      total<ε = begin<
        fst (inner +₊ outer) ≤⟨ total≤six-q ⟩
        fst six-q <⟨ six-q<eight-q ⟩
        fst eight-q ≡→≤⟨ eight-q≡ε/2 ⟩
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

      xδ∼xζ = cx δ ζ
      xζ∼xη = cx' ζ η
      xδ∼xη = isTriangular∼̂ (x δ) (x ζ) (x η)
        (a +₊ c) (d +₊ b) xδ∼xζ xζ∼xη
      enlarged = isMonotone∼̂< _ _ inner target inner<target xδ∼xη
  in lim-lim x g x g' ε δ η cx cx' Δ enlarged


g-irrelevant : ∀ x g g' cx cx' → lim x g cx ≡ lim x g' cx'
g-irrelevant x g g' cx cx' =
  g-irrelevant-with x g g' cx cx' (monotoneJointSmallSelector g g')


lim-from₁ : (x : ℚ₊ → ℭ̂)
      → ∃[ g ∈ Γ ] (∀ ε δ → x ε ∼̂[ (g .γ ε) +₊ (g .γ δ) ] x δ)
      → ℭ̂
lim-from₁ x = PT.Rec→Set.go w
 where
 w : Rec→Set ℭ̂
 w .Rec→Set.isSetB = isSetℭ̂
 w .Rec→Set.f (g , cx) = lim x g cx
 w .Rec→Set.fconst _ _ = g-irrelevant _ _ _ _ _
