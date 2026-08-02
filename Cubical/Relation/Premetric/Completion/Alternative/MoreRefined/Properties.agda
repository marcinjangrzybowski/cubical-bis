open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.Alternative.MoreRefined.Properties
  {ℓ} {ℓ'} (M' : PremetricSpace ℓ ℓ') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import Cubical.Data.Sigma
open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order as ℕ

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.Ring
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Base as ℚ
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Rationals.Order as ℚ
  renaming (_<_ to _<ℚ_ ; _≤_ to _≤ℚ_)

import Cubical.Relation.Premetric.Completion.Alternative.MoreRefined.Base
  as MoreRefinedDefinition

module S = MoreRefinedDefinition M'
module PM = PremetricStr (M' .snd)

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ
open OrderedCommRingStr (snd ℚOrderedCommRing)
open OrderedCommRingTheory ℚOrderedCommRing
open OrderedCommRingReasoning ℚOrderedCommRing

private
  module ℚRing = RingTheory (OrderedCommRing→Ring ℚOrderedCommRing)

  tightenLimitRadius : ∀ (ε δ κ gap : ℚ₊) →
    fst gap ≡ fst ε ℚ.- fst δ → κ <₊ gap →
    (κ +₊ δ) <₊ ε
  tightenLimitRadius ε δ κ gap gap≡ε-δ κ<gap = begin<
    fst (κ +₊ δ)
      <⟨ +MonoR< (fst κ) (fst gap) (fst δ) κ<gap ⟩
    fst (gap +₊ δ)
      ≡→≤⟨ cong (ℚ._+ fst δ) gap≡ε-δ ⟩
    (fst ε ℚ.- fst δ) ℚ.+ fst δ
      ≡→≤⟨ minusPlus₊ ε δ ⟩
    fst ε ◾

  restoredDifference : ∀ (κ δ : ℚ₊) →
    (κ +₊ δ) -₊ δ ≡ fst κ
  restoredDifference κ δ = ℚRing.plusMinus (fst κ) (fst δ)

  tripleQuarter< : ∀ ε → ((ε /4₊ +₊ ε /4₊) +₊ ε /4₊) <₊ ε
  tripleQuarter< ε = begin<
    fst ((ε /4₊ +₊ ε /4₊) +₊ ε /4₊)
      ≡→≤⟨ cong (ℚ._+ fst (ε /4₊)) (/4+/4≡/2 (fst ε)) ⟩
    fst (ε /2₊ +₊ ε /4₊)
      <⟨ +MonoL< (fst (ε /4₊)) (fst (ε /2₊))
           (fst (ε /2₊)) (/4₊</2₊ ε) ⟩
    fst (ε /2₊ +₊ ε /2₊)
      ≡→≤⟨ /2+/2≡id (fst ε) ⟩
    fst ε ◾


-- An injected point which occurs sufficiently late in a represented
-- sequence is close to the sequence limit.  The lemma is deliberately
-- asymmetric: this is the constructor shape needed for density arguments.

ι-close-lim-from-late : ∀ q x gx N xc ε n →
  N (ε /4₊) ℕ.≤ n →
  S.ι q S.∼̂ₛ[ ε /4₊ ] x n →
  S.ι q S.∼̂ₛ[ ε ] S.lim x gx
ι-close-lim-from-late q x gx N xc ε n Nδ≤n ιq∼xn =
  subst (S.ι q S.∼̂ₛ[ ε ]_)
    (cong (S.lim x) (squash₁ ∣ N , xc ∣₁ gx)) concrete
  where
  δ = ε /4₊

  x-n∼x-Nδ : x n S.∼̂ₛ[ δ ] x (N δ)
  x-n∼x-Nδ = xc δ n (N δ) Nδ≤n ℕ.≤-refl

  small : S.ι q S.∼̂ₛ[ δ +₊ δ ] x (N δ)
  small = S.tri∼ (S.ι q) (x n) (x (N δ)) δ δ
    ιq∼xn x-n∼x-Nδ

  Δ : 0 ℚ.< ε -₊ δ
  Δ = <→0<Δ (fst δ) (fst ε) (/4₊<id ε)

  target = (ε -₊ δ , Δ)

  small<target : (δ +₊ δ) <₊ target
  small<target = +CancelR<
    (fst (δ +₊ δ)) (fst target) (fst δ)
    (subst (fst (δ +₊ δ) ℚ.+ fst δ <ℚ_)
      (sym (minusPlus₊ ε δ)) (tripleQuarter< ε))

  concrete : S.ι q S.∼̂ₛ[ ε ] S.lim x ∣ N , xc ∣₁
  concrete = S.ι-lim q x N ε δ xc Δ
    (S.isMonotone∼̂ₛ< _ _ _ target small<target small)


-- The rational injection is merely dense at every requested radius.  No
-- sequence of choices is produced: each approximation remains truncated.

∃approx : ∀ x ε → ∃[ q ∈ M' .fst ] (S.ι q S.∼̂ₛ[ ε ] x)
∃approx = S.Elimℭ̂ₛ-Prop.go e
  where
  e : S.Elimℭ̂ₛ-Prop (λ x → ∀ ε → ∃[ q ∈ M' .fst ] (S.ι q S.∼̂ₛ[ ε ] x))
  e .S.Elimℭ̂ₛ-Prop.ιA q ε = ∣ q , S.isRefl∼̂ₛ (S.ι q) ε ∣₁
  e .S.Elimℭ̂ₛ-Prop.limA x gx IH ε =
    PT.rec squash₁ withCauchy gx
    where
    withCauchy : S.CauchySeq x →
      ∃[ q ∈ M' .fst ] (S.ι q S.∼̂ₛ[ ε ] S.lim x gx)
    withCauchy (N , xc) = PT.map
      (λ { (q , ιq∼xn) → q ,
        ι-close-lim-from-late q x gx N xc ε (N (ε /4₊))
          ℕ.≤-refl ιq∼xn })
      (IH (N (ε /4₊)) (ε /4₊))
  e .S.Elimℭ̂ₛ-Prop.isPropA x = isPropΠ λ _ → squash₁


-- Roundedness is structural for the sequence-backed relation.  In a limit
-- constructor, first tighten the recursive inner radius and then add back
-- the displayed sampling cost.  Monotonicity constructors are even simpler:
-- their original radius is already a strict smaller witness.

isRounded∼̂ₛ : ∀ x y ε →
  x S.∼̂ₛ[ ε ] y →
  ∃[ δ ∈ ℚ₊ ] (δ <₊ ε) × (x S.∼̂ₛ[ δ ] y)
isRounded∼̂ₛ .(S.ι x) .(S.ι y) ε (S.ι-ι x y .ε x≈y) =
  PT.map (λ { (δ , δ<ε , x≈δy) →
    δ , δ<ε , S.ι-ι x y δ x≈δy })
    (PM.isRounded≈ x y ε x≈y)
isRounded∼̂ₛ .(S.ι x) .(S.lim y ∣ N , yc ∣₁) ε
  (S.ι-lim x y N .ε δ yc Δ inner) =
  PT.map tighten (isRounded∼̂ₛ _ _ (ε -₊ δ , Δ) inner)
  where
  tighten : Σ[ κ ∈ ℚ₊ ]
      (κ <₊ (ε -₊ δ , Δ)) ×
      (S.ι x S.∼̂ₛ[ κ ] y (N δ)) →
    Σ[ ρ ∈ ℚ₊ ] (ρ <₊ ε) ×
      (S.ι x S.∼̂ₛ[ ρ ] S.lim y ∣ N , yc ∣₁)
  tighten (κ , κ<ε-δ , innerκ) = ρ , ρ<ε ,
    S.ι-lim x y N ρ δ yc Δρ innerρ
    where
    δ<ε : δ <₊ ε
    δ<ε = 0<Δ→< (fst δ) (fst ε) Δ

    ρ = κ +₊ δ
    ρ<ε : ρ <₊ ε
    ρ<ε = tightenLimitRadius ε δ κ (ε -₊ δ , Δ) refl κ<ε-δ

    difference≡κ : ρ -₊ δ ≡ fst κ
    difference≡κ = restoredDifference κ δ

    Δρ : 0 <ℚ ρ -₊ δ
    Δρ = subst (0 <ℚ_) (sym difference≡κ) (snd κ)

    innerρ : S.ι x S.∼̂ₛ[ ρ -₊ δ , Δρ ] y (N δ)
    innerρ = subst (S.ι x S.∼̂ₛ[_] y (N δ))
      (ℚ₊≡ (sym difference≡κ)) innerκ
isRounded∼̂ₛ .(S.lim x ∣ N , xc ∣₁) .(S.ι y) ε
  (S.lim-ι x N y .ε δ xc Δ inner) =
  PT.map tighten (isRounded∼̂ₛ _ _ (ε -₊ δ , Δ) inner)
  where
  tighten : Σ[ κ ∈ ℚ₊ ]
      (κ <₊ (ε -₊ δ , Δ)) ×
      (x (N δ) S.∼̂ₛ[ κ ] S.ι y) →
    Σ[ ρ ∈ ℚ₊ ] (ρ <₊ ε) ×
      (S.lim x ∣ N , xc ∣₁ S.∼̂ₛ[ ρ ] S.ι y)
  tighten (κ , κ<ε-δ , innerκ) = ρ , ρ<ε ,
    S.lim-ι x N y ρ δ xc Δρ innerρ
    where
    δ<ε : δ <₊ ε
    δ<ε = 0<Δ→< (fst δ) (fst ε) Δ

    ρ = κ +₊ δ
    ρ<ε : ρ <₊ ε
    ρ<ε = tightenLimitRadius ε δ κ (ε -₊ δ , Δ) refl κ<ε-δ

    difference≡κ : ρ -₊ δ ≡ fst κ
    difference≡κ = restoredDifference κ δ

    Δρ : 0 <ℚ ρ -₊ δ
    Δρ = subst (0 <ℚ_) (sym difference≡κ) (snd κ)

    innerρ : x (N δ) S.∼̂ₛ[ ρ -₊ δ , Δρ ] S.ι y
    innerρ = subst (x (N δ) S.∼̂ₛ[_] S.ι y)
      (ℚ₊≡ (sym difference≡κ)) innerκ
isRounded∼̂ₛ .(S.lim x ∣ N , xc ∣₁) .(S.lim y ∣ K , yc ∣₁) ε
  (S.lim-lim x N y K .ε δ η xc yc Δ inner) =
  PT.map tighten (isRounded∼̂ₛ _ _ (ε -₊ (δ +₊ η) , Δ) inner)
  where
  outer = δ +₊ η

  tighten : Σ[ κ ∈ ℚ₊ ]
      (κ <₊ (ε -₊ outer , Δ)) ×
      (x (N δ) S.∼̂ₛ[ κ ] y (K η)) →
    Σ[ ρ ∈ ℚ₊ ] (ρ <₊ ε) ×
      (S.lim x ∣ N , xc ∣₁ S.∼̂ₛ[ ρ ] S.lim y ∣ K , yc ∣₁)
  tighten (κ , κ<ε-outer , innerκ) = ρ , ρ<ε ,
    S.lim-lim x N y K ρ δ η xc yc Δρ innerρ
    where
    outer<ε : outer <₊ ε
    outer<ε = 0<Δ→< (fst outer) (fst ε) Δ

    ρ = κ +₊ outer
    ρ<ε : ρ <₊ ε
    ρ<ε = tightenLimitRadius ε outer κ (ε -₊ outer , Δ) refl κ<ε-outer

    difference≡κ : ρ -₊ outer ≡ fst κ
    difference≡κ = restoredDifference κ outer

    Δρ : 0 <ℚ ρ -₊ outer
    Δρ = subst (0 <ℚ_) (sym difference≡κ) (snd κ)

    innerρ : x (N δ) S.∼̂ₛ[ ρ -₊ outer , Δρ ] y (K η)
    innerρ = subst (x (N δ) S.∼̂ₛ[_] y (K η))
      (ℚ₊≡ (sym difference≡κ)) innerκ
isRounded∼̂ₛ x y .δ (S.mono∼ .x .y ε δ ε<δ p) =
  ∣ ε , ε<δ , p ∣₁
isRounded∼̂ₛ .y .x ε (S.sym∼ x y .ε p) =
  PT.map (λ { (δ , δ<ε , q) → δ , δ<ε , S.sym∼ x y δ q })
    (isRounded∼̂ₛ x y ε p)
isRounded∼̂ₛ .x .z .(ε +₊ δ) (S.tri∼ x y z ε δ p q) =
  PT.map2 combine (isRounded∼̂ₛ x y ε p) (isRounded∼̂ₛ y z δ q)
  where
  combine :
    (Σ[ ε' ∈ ℚ₊ ] (ε' <₊ ε) × (x S.∼̂ₛ[ ε' ] y)) →
    (Σ[ δ' ∈ ℚ₊ ] (δ' <₊ δ) × (y S.∼̂ₛ[ δ' ] z)) →
    Σ[ ρ ∈ ℚ₊ ] (ρ <₊ (ε +₊ δ)) × (x S.∼̂ₛ[ ρ ] z)
  combine (ε' , ε'<ε , p') (δ' , δ'<δ , q') =
    ε' +₊ δ' , +Mono< _ _ _ _ ε'<ε δ'<δ ,
    S.tri∼ x y z ε' δ' p' q'
isRounded∼̂ₛ x y ε (S.isProp∼ .x .ε .y p q i) =
  isProp→PathP (λ _ → squash₁)
    (isRounded∼̂ₛ x y ε p) (isRounded∼̂ₛ x y ε q) i


ℭ̂ₛPremetricSpace : PremetricSpace (ℓ-max ℓ ℓ') (ℓ-max ℓ ℓ')
ℭ̂ₛPremetricSpace .fst = S.ℭ̂ₛ
PremetricStr._≈[_]_ (ℭ̂ₛPremetricSpace .snd) = S._∼̂ₛ[_]_
PremetricStr.isPremetric (ℭ̂ₛPremetricSpace .snd) .IsPremetric.isSetM = S.isSetℭ̂ₛ
PremetricStr.isPremetric (ℭ̂ₛPremetricSpace .snd) .IsPremetric.isProp≈ =
  λ x y ε → S.isProp∼ x ε y
PremetricStr.isPremetric (ℭ̂ₛPremetricSpace .snd) .IsPremetric.isRefl≈ = S.isRefl∼̂ₛ
PremetricStr.isPremetric (ℭ̂ₛPremetricSpace .snd) .IsPremetric.isSym≈ = S.sym∼
PremetricStr.isPremetric (ℭ̂ₛPremetricSpace .snd) .IsPremetric.isSeparated≈ = S.eqℭ
PremetricStr.isPremetric (ℭ̂ₛPremetricSpace .snd) .IsPremetric.isTriangular≈ = S.tri∼
PremetricStr.isPremetric (ℭ̂ₛPremetricSpace .snd) .IsPremetric.isRounded≈ = isRounded∼̂ₛ
