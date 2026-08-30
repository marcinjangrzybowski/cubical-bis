open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.Alternative.Sequential.Comparison.TruncatedScale.From
  {ℓ} {ℓ'} (M' : PremetricSpace ℓ ℓ') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.NatPlusOne
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals
open import Cubical.Algebra.Ring

open import Cubical.Data.Rationals.Base hiding (isProp∼)
open import Cubical.Data.Rationals.Inverse
open import Cubical.Data.Rationals.Order as ℚ
  renaming (_<_ to _<ℚ_ ; _≤_ to _≤ℚ_)
open import Cubical.Data.Rationals.Order.Algebra as ℚ
import Cubical.Data.Rationals.Properties as ℚ

import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Base
  as SequentialDefinition
import Cubical.Relation.Premetric.Completion.Alternative.TruncatedScale
  as TruncatedScaleDefinition

module S = SequentialDefinition M'
module R = TruncatedScaleDefinition M'

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ
open OrderedCommRingReasoning ℚOrderedCommRing
open OrderedCommRingTheory ℚOrderedCommRing
open OrderedCommRingStr (snd ℚOrderedCommRing)

private
  module PM = PremetricStr (M' .snd)
  module ℚRing = RingTheory (OrderedCommRing→Ring ℚOrderedCommRing)


-- The reverse interpretation needs an arbitrarily small amount of radius
-- when a Γ-indexed family is replaced by a natural subsequence.

Slack : S.ℭ̂ₛ → S.ℭ̂ₛ → ℚ₊ → Type _
Slack x y ε = ∀ δ → ε <₊ δ → x S.∼̂ₛ[ δ ] y

private
  isPropSlack : ∀ x y ε → isProp (Slack x y ε)
  isPropSlack x y ε = isPropΠ2 λ δ _ → S.isProp∼ x δ y

  slackMono : ∀ x y ε δ → ε <₊ δ →
    Slack x y ε → Slack x y δ
  slackMono x y ε δ ε<δ p ρ δ<ρ =
    p ρ (ℚ.isTrans< _ _ _ ε<δ δ<ρ)

  slackSym : ∀ x y ε → Slack x y ε → Slack y x ε
  slackSym x y ε p δ ε<δ = S.sym∼ x y δ (p δ ε<δ)

  reassociate4₊ : ∀ (a b c d : ℚ₊) →
    fst ((a +₊ b) +₊ (c +₊ d)) ≡
      fst ((a +₊ c) +₊ (b +₊ d))
  reassociate4₊ a b c d =
      sym (ℚ.+Assoc (fst a) (fst b) (fst (c +₊ d)))
    ∙ cong (fst a ℚ.+_)
        (ℚRing.+Assoc-comm1 (fst b) (fst c) (fst d))
    ∙ ℚ.+Assoc (fst a) (fst c) (fst (b +₊ d))

  slackTri : ∀ x y z ε δ →
    Slack x y ε → Slack y z δ → Slack x z (ε +₊ δ)
  slackTri x y z ε δ p q ρ sum<ρ =
    S.isMonotone∼̂ₛ< x z (leftRadius +₊ rightRadius) ρ
      combined<ρ (S.tri∼ x y z leftRadius rightRadius left right)
    where
    Δ = <→0<Δ (fst (ε +₊ δ)) (fst ρ) sum<ρ
    gap = (ρ -₊ (ε +₊ δ) , Δ)
    t = gap /4₊
    leftRadius = ε +₊ t
    rightRadius = δ +₊ t

    left : x S.∼̂ₛ[ leftRadius ] y
    left = p leftRadius (<₊SumLeft ε t)

    right : y S.∼̂ₛ[ rightRadius ] z
    right = q rightRadius (<₊SumLeft δ t)

    two-t<gap : fst (t +₊ t) <ℚ fst gap
    two-t<gap = begin<
      fst (t +₊ t) ≡→≤⟨ /4+/4≡/2 (fst gap) ⟩
      fst (gap /2₊) <⟨ /2₊<id gap ⟩
      fst gap ◾

    combined<ρ : fst (leftRadius +₊ rightRadius) <ℚ fst ρ
    combined<ρ = begin<
      fst (leftRadius +₊ rightRadius)
        ≡→≤⟨ reassociate4₊ ε t δ t ⟩
      fst ((ε +₊ δ) +₊ (t +₊ t))
        <⟨ +MonoL< _ _ (fst (ε +₊ δ)) two-t<gap ⟩
      fst ((ε +₊ δ) +₊ gap)
        ≡→≤⟨ ℚ.+Comm (fst (ε +₊ δ)) (fst gap)
          ∙ minusPlus₊ ρ (ε +₊ δ) ⟩
      fst ρ ◾

  slackEq : ∀ x y → (∀ ε → Slack x y ε) → x ≡ y
  slackEq x y p = S.eqℭ x y λ ε →
    p (ε /2₊) ε (/2₊<id ε)

  positiveDifference : ∀ ε a → 0 ℚ.< ε -₊ a → ℚ₊
  positiveDifference ε a Δ = ε -₊ a , Δ

  oneBridge : ∀ (ε a b : ℚ₊) (Δ : 0 ℚ.< ε -₊ a) →
    fst (positiveDifference ε a Δ +₊ (a +₊ b)) ≡
      fst (ε +₊ b)
  oneBridge ε a b Δ =
      ℚ.+Assoc (fst (positiveDifference ε a Δ))
        (fst a) (fst b)
    ∙ cong (ℚ._+ fst b) (minusPlus₊ ε a)

  threeBridge : ∀ (ε a b c d : ℚ₊)
    (Δ : 0 ℚ.< ε -₊ (a +₊ b)) →
    fst ((c +₊ a) +₊
      (positiveDifference ε (a +₊ b) Δ +₊ (b +₊ d))) ≡
      fst (ε +₊ (c +₊ d))
  threeBridge ε a b c d Δ =
      ℚ.+Assoc (fst (c +₊ a))
        (fst (positiveDifference ε (a +₊ b) Δ)) (fst (b +₊ d))
    ∙ cong (ℚ._+ fst (b +₊ d))
        (ℚ.+Comm (fst (c +₊ a))
          (fst (positiveDifference ε (a +₊ b) Δ)))
    ∙ sym (ℚ.+Assoc (fst (positiveDifference ε (a +₊ b) Δ))
        (fst (c +₊ a)) (fst (b +₊ d)))
    ∙ cong (λ z → fst (positiveDifference ε (a +₊ b) Δ) ℚ.+ z)
        (cong (ℚ._+ fst (b +₊ d)) (ℚ.+Comm (fst c) (fst a))
        ∙ reassociate4₊ a c b d)
    ∙ oneBridge ε (a +₊ b) (c +₊ d) Δ

private
  dyadic : ℕ → ℚ₊
  dyadic n = [ 1 / 2 ]₊ ℚ₊^ⁿ n

  half<one : fst [ 1 / 2 ]₊ <ℚ 1
  half<one = subst (fst [ 1 / 2 ]₊ <ℚ_)
    (/2+/2≡id 1) (<₊SumLeft [ 1 / 2 ]₊ [ 1 / 2 ]₊)

  dyadicAntitone : ∀ m n → m ℕ.≤ n →
    fst (dyadic n) ≤ℚ fst (dyadic m)
  dyadicAntitone m n m≤n =
    powExponentAntitone (fst [ 1 / 2 ]₊)
      (OrderedCommRingStr.<-≤-weaken (snd ℚOrderedCommRing)
        _ _ (snd [ 1 / 2 ]₊))
      (OrderedCommRingStr.<-≤-weaken (snd ℚOrderedCommRing)
        _ _ half<one)
      m n m≤n

  modulus : ℚ₊ → ℕ
  modulus ε = fst (1/2ⁿ<ε (ε /4₊))

  modulus-small : ∀ ε →
    fst (dyadic (modulus ε)) <ℚ fst (ε /4₊)
  modulus-small ε = snd (1/2ⁿ<ε (ε /4₊))

  Sample : (ℚ₊ → S.ℭ̂ₛ) → Γ → ℕ → S.ℭ̂ₛ
  Sample x g n = x (g .Γ.τ (dyadic n))

  sampleCauchy : ∀ (x : ℚ₊ → S.ℭ̂ₛ) g
    → (∀ ε δ →
        Slack (x ε) (x δ) (g .Γ.γ ε +₊ g .Γ.γ δ))
    → S.CauchySeq (Sample x g)
  sampleCauchy x g xc .fst = modulus
  sampleCauchy x g xc .snd ε m n N≤m N≤n =
    xc (g .Γ.τ (dyadic m)) (g .Γ.τ (dyadic n)) ε scale<ε
    where
    q = ε /4₊

    gm<q : fst (g .Γ.γ (g .Γ.τ (dyadic m))) <ℚ fst q
    gm<q = begin<
      fst (g .Γ.γ (g .Γ.τ (dyadic m)))
        ≤⟨ g .Γ.γ∘τ≤id (dyadic m) ⟩
      fst (dyadic m)
        ≤⟨ dyadicAntitone (modulus ε) m N≤m ⟩
      fst (dyadic (modulus ε))
        <⟨ modulus-small ε ⟩
      fst q ◾

    gn<q : fst (g .Γ.γ (g .Γ.τ (dyadic n))) <ℚ fst q
    gn<q = begin<
      fst (g .Γ.γ (g .Γ.τ (dyadic n)))
        ≤⟨ g .Γ.γ∘τ≤id (dyadic n) ⟩
      fst (dyadic n)
        ≤⟨ dyadicAntitone (modulus ε) n N≤n ⟩
      fst (dyadic (modulus ε))
        <⟨ modulus-small ε ⟩
      fst q ◾

    scale<ε :
      fst (g .Γ.γ (g .Γ.τ (dyadic m)) +₊
        g .Γ.γ (g .Γ.τ (dyadic n))) <ℚ fst ε
    scale<ε = begin<
      fst (g .Γ.γ (g .Γ.τ (dyadic m)) +₊
        g .Γ.γ (g .Γ.τ (dyadic n)))
        <⟨ +Mono< _ _ _ _ gm<q gn<q ⟩
      fst (q +₊ q) ≡→≤⟨ /4+/4≡/2 (fst ε) ⟩
      fst (ε /2₊) <⟨ /2₊<id ε ⟩
      fst ε ◾

  gammaSeqLimitWith : (x : ℚ₊ → S.ℭ̂ₛ) →
    Σ[ g ∈ Γ ]
      (∀ ε δ → Slack (x ε) (x δ)
        (g .Γ.γ ε +₊ g .Γ.γ δ))
    → S.ℭ̂ₛ
  gammaSeqLimitWith x (g , xc) =
    S.lim (Sample x g) ∣ sampleCauchy x g xc ∣₁


private
  gammaSeqLimitWith-independent : ∀ x gx gy →
    gammaSeqLimitWith x gx ≡ gammaSeqLimitWith x gy
  gammaSeqLimitWith-independent x (g , xc) (h , yc) =
    S.eqℭ _ _ close
    where
    X = Sample x g
    Y = Sample x h
    Xw = sampleCauchy x g xc
    Yw = sampleCauchy x h yc
    Xc = snd Xw
    Yc = snd Yw

    close : ∀ ε →
      S.lim X ∣ Xw ∣₁ S.∼̂ₛ[ ε ] S.lim Y ∣ Yw ∣₁
    close ε =
      let r = ε /4₊ /2₊
          q = r /4₊
          a = g .Γ.τ (dyadic (modulus r))
          b = h .Γ.τ (dyadic (modulus r))
          ζ = min₊ (g .Γ.τ q) (h .Γ.τ q) /2₊

          ga<q : fst (g .Γ.γ a) <ℚ fst q
          ga<q = begin<
            fst (g .Γ.γ a) ≤⟨ g .Γ.γ∘τ≤id _ ⟩
            fst (dyadic (modulus r)) <⟨ modulus-small r ⟩
            fst q ◾

          gb<q : fst (h .Γ.γ b) <ℚ fst q
          gb<q = begin<
            fst (h .Γ.γ b) ≤⟨ h .Γ.γ∘τ≤id _ ⟩
            fst (dyadic (modulus r)) <⟨ modulus-small r ⟩
            fst q ◾

          gζ<q : fst (g .Γ.γ ζ) <ℚ fst q
          gζ<q = begin<
            fst (g .Γ.γ ζ)
              <⟨ g .Γ.mon-γ ζ (g .Γ.τ q)
                (min/2₊<L (g .Γ.τ q) (h .Γ.τ q)) ⟩
            fst (g .Γ.γ (g .Γ.τ q)) ≤⟨ g .Γ.γ∘τ≤id q ⟩
            fst q ◾

          hζ<q : fst (h .Γ.γ ζ) <ℚ fst q
          hζ<q = begin<
            fst (h .Γ.γ ζ)
              <⟨ h .Γ.mon-γ ζ (h .Γ.τ q)
                (min/2₊<R (g .Γ.τ q) (h .Γ.τ q)) ⟩
            fst (h .Γ.γ (h .Γ.τ q)) ≤⟨ h .Γ.γ∘τ≤id q ⟩
            fst q ◾

          ga+gζ<r : fst (g .Γ.γ a +₊ g .Γ.γ ζ) <ℚ fst r
          ga+gζ<r = begin<
            fst (g .Γ.γ a +₊ g .Γ.γ ζ)
              <⟨ +Mono< _ _ _ _ ga<q gζ<q ⟩
            fst (q +₊ q) ≡→≤⟨ /4+/4≡/2 (fst r) ⟩
            fst (r /2₊) <⟨ /2₊<id r ⟩
            fst r ◾

          hζ+hb<r : fst (h .Γ.γ ζ +₊ h .Γ.γ b) <ℚ fst r
          hζ+hb<r = begin<
            fst (h .Γ.γ ζ +₊ h .Γ.γ b)
              <⟨ +Mono< _ _ _ _ hζ<q gb<q ⟩
            fst (q +₊ q) ≡→≤⟨ /4+/4≡/2 (fst r) ⟩
            fst (r /2₊) <⟨ /2₊<id r ⟩
            fst r ◾

          left : x a S.∼̂ₛ[ r ] x ζ
          left = xc a ζ r ga+gζ<r

          right : x ζ S.∼̂ₛ[ r ] x b
          right = yc ζ b r hζ+hb<r

          inner = r +₊ r
          outer = r +₊ r
          cross : X (modulus r) S.∼̂ₛ[ inner ] Y (modulus r)
          cross = S.tri∼ _ _ _ r r left right

          four-r≡ε/2 : fst ((r +₊ r) +₊ (r +₊ r)) ≡ fst (ε /2₊)
          four-r≡ε/2 =
              cong (λ z → z ℚ.+ z) (/2+/2≡id (fst (ε /4₊)))
            ∙ /4+/4≡/2 (fst ε)

          total<ε : fst (inner +₊ outer) <ℚ fst ε
          total<ε = begin<
            fst (inner +₊ outer) ≡→≤⟨ four-r≡ε/2 ⟩
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
            (subst (fst inner ℚ.+ fst outer <ℚ_)
              (sym (minusPlus₊ ε outer)) total<ε)
      in S.lim-lim X modulus Y modulus ε r r Xc Yc Δ
        (S.isMonotone∼̂ₛ< _ _ inner target inner<target cross)

  GammaData : (ℚ₊ → S.ℭ̂ₛ) → Type _
  GammaData x =
    Σ[ g ∈ Γ ]
      (∀ ε δ → Slack (x ε) (x δ)
        (g .Γ.γ ε +₊ g .Γ.γ δ))

  gammaSeqLimitRec : (x : ℚ₊ → S.ℭ̂ₛ) →
    PT.Rec→Set {A = GammaData x} S.ℭ̂ₛ
  gammaSeqLimitRec x .PT.Rec→Set.isSetB = S.isSetℭ̂ₛ
  gammaSeqLimitRec x .PT.Rec→Set.f = gammaSeqLimitWith x
  gammaSeqLimitRec x .PT.Rec→Set.fconst = gammaSeqLimitWith-independent x

  chooseGammaSeqLimit : (x : ℚ₊ → S.ℭ̂ₛ) →
    ∥ GammaData x ∥₁ → S.ℭ̂ₛ
  chooseGammaSeqLimit x = PT.Rec→Set.go (gammaSeqLimitRec x)

  chooseGammaSeqLimit-β : ∀ x g xc →
    chooseGammaSeqLimit x ∣ g , xc ∣₁ ≡
      S.lim (Sample x g) ∣ sampleCauchy x g xc ∣₁
  chooseGammaSeqLimit-β x g xc =
    PT.Rec→Set.β-go (gammaSeqLimitRec x) (g , xc)


private
  slackIotaLim : ∀ x y g ε δ yc Δ →
    Slack (S.ι x) (y δ) (ε -₊ g .Γ.γ δ , Δ) →
    Slack (S.ι x)
      (S.lim (Sample y g) ∣ sampleCauchy y g yc ∣₁) ε
  slackIotaLim x y g ε δ yc Δ inner ρ ε<ρ =
    S.ι-lim x (Sample y g) modulus ρ r
      (sampleCauchy y g yc .snd) Δr direct
    where
    gapΔ : 0 ℚ.< ρ -₊ ε
    gapΔ = <→0<Δ (fst ε) (fst ρ) ε<ρ

    gap : ℚ₊
    gap = (ρ -₊ ε , gapΔ)

    r : ℚ₊
    r = gap /4₊

    a : ℚ₊
    a = g .Γ.τ (dyadic (modulus r))

    ga<r/4 : fst (g .Γ.γ a) <ℚ fst (r /4₊)
    ga<r/4 = begin<
      fst (g .Γ.γ a) ≤⟨ g .Γ.γ∘τ≤id _ ⟩
      fst (dyadic (modulus r)) <⟨ modulus-small r ⟩
      fst (r /4₊) ◾

    ga<r : fst (g .Γ.γ a) <ℚ fst r
    ga<r = ℚ.isTrans< _ _ _ ga<r/4 (/4₊<id r)

    ga+r<gap : fst (g .Γ.γ a +₊ r) <ℚ fst gap
    ga+r<gap = begin<
      fst (g .Γ.γ a +₊ r)
        <⟨ +MonoR< _ _ (fst r) ga<r ⟩
      fst (r +₊ r) ≡→≤⟨ /4+/4≡/2 (fst gap) ⟩
      fst (gap /2₊) <⟨ /2₊<id gap ⟩
      fst gap ◾

    gδ<ε : g .Γ.γ δ <₊ ε
    gδ<ε = 0<Δ→< _ _ Δ

    base : ℚ₊
    base = (ε -₊ g .Γ.γ δ , Δ) +₊
      (g .Γ.γ δ +₊ g .Γ.γ a)

    base+r<ρ : fst (base +₊ r) <ℚ fst ρ
    base+r<ρ = begin<
      fst (base +₊ r)
        ≡→≤⟨ cong (ℚ._+ fst r)
          (oneBridge ε (g .Γ.γ δ) (g .Γ.γ a) Δ)
          ∙ sym (ℚ.+Assoc (fst ε) (fst (g .Γ.γ a)) (fst r)) ⟩
      fst ε ℚ.+ fst (g .Γ.γ a +₊ r)
        <⟨ +MonoL< _ _ (fst ε) ga+r<gap ⟩
      fst (ε +₊ gap)
        ≡→≤⟨ ℚ.+Comm (fst ε) (fst gap) ∙ minusPlus₊ ρ ε ⟩
      fst ρ ◾

    r<ρ : r <₊ ρ
    r<ρ = begin<
      fst r <⟨ /4₊<id gap ⟩
      fst gap <⟨ Δ<₊ ρ ε ⟩
      fst ρ ◾

    Δr : 0 ℚ.< ρ -₊ r
    Δr = <→0<Δ (fst r) (fst ρ) r<ρ

    target : ℚ₊
    target = (ρ -₊ r , Δr)

    base<target : base <₊ target
    base<target = +CancelR< (fst base) (fst target) (fst r)
      (subst (fst (base +₊ r) <ℚ_)
        (sym (minusPlus₊ ρ r)) base+r<ρ)

    direct : S.ι x S.∼̂ₛ[ target ] y a
    direct =
      slackTri (S.ι x) (y δ) (y a)
        (ε -₊ g .Γ.γ δ , Δ)
        (g .Γ.γ δ +₊ g .Γ.γ a)
        inner (yc δ a) target base<target

  slackLimIota : ∀ x g y ε δ xc Δ →
    Slack (x δ) (S.ι y) (ε -₊ g .Γ.γ δ , Δ) →
    Slack
      (S.lim (Sample x g) ∣ sampleCauchy x g xc ∣₁)
      (S.ι y) ε
  slackLimIota x g y ε δ xc Δ inner =
    slackSym _ _ ε
      (slackIotaLim y x g ε δ xc Δ
        (slackSym _ _ (ε -₊ g .Γ.γ δ , Δ) inner))

  slackLimLim : ∀ x g y h ε δ η xc yc Δ →
    Slack (x δ) (y η)
      (ε -₊ (g .Γ.γ δ +₊ h .Γ.γ η) , Δ) →
    Slack
      (S.lim (Sample x g) ∣ sampleCauchy x g xc ∣₁)
      (S.lim (Sample y h) ∣ sampleCauchy y h yc ∣₁) ε
  slackLimLim x g y h ε δ η xc yc Δ inner ρ ε<ρ =
    S.lim-lim (Sample x g) modulus (Sample y h) modulus
      ρ r r (sampleCauchy x g xc .snd) (sampleCauchy y h yc .snd)
      Δouter direct
    where
    gapΔ : 0 ℚ.< ρ -₊ ε
    gapΔ = <→0<Δ (fst ε) (fst ρ) ε<ρ

    gap : ℚ₊
    gap = (ρ -₊ ε , gapΔ)

    r : ℚ₊
    r = gap /4₊

    outer : ℚ₊
    outer = r +₊ r

    a : ℚ₊
    a = g .Γ.τ (dyadic (modulus r))

    b : ℚ₊
    b = h .Γ.τ (dyadic (modulus r))

    ga<r/4 : fst (g .Γ.γ a) <ℚ fst (r /4₊)
    ga<r/4 = begin<
      fst (g .Γ.γ a) ≤⟨ g .Γ.γ∘τ≤id _ ⟩
      fst (dyadic (modulus r)) <⟨ modulus-small r ⟩
      fst (r /4₊) ◾

    hb<r/4 : fst (h .Γ.γ b) <ℚ fst (r /4₊)
    hb<r/4 = begin<
      fst (h .Γ.γ b) ≤⟨ h .Γ.γ∘τ≤id _ ⟩
      fst (dyadic (modulus r)) <⟨ modulus-small r ⟩
      fst (r /4₊) ◾

    sample<r : fst (g .Γ.γ a +₊ h .Γ.γ b) <ℚ fst r
    sample<r = begin<
      fst (g .Γ.γ a +₊ h .Γ.γ b)
        <⟨ +Mono< _ _ _ _ ga<r/4 hb<r/4 ⟩
      fst (r /4₊ +₊ r /4₊) ≡→≤⟨ /4+/4≡/2 (fst r) ⟩
      fst (r /2₊) <⟨ /2₊<id r ⟩
      fst r ◾

    tail<gap :
      fst ((g .Γ.γ a +₊ h .Γ.γ b) +₊ outer) <ℚ fst gap
    tail<gap = begin<
      fst ((g .Γ.γ a +₊ h .Γ.γ b) +₊ outer)
        <⟨ +MonoR< _ _ (fst outer) sample<r ⟩
      fst (r +₊ outer)
        <⟨ +MonoL< _ _ (fst r) (<₊SumRight outer r) ⟩
      fst (r +₊ (r +₊ outer))
        ≡→≤⟨ ℚ.+Assoc (fst r) (fst r) (fst outer)
          ∙ /4+/4+/4+/4≡id (fst gap) ⟩
      fst gap ◾

    base : ℚ₊
    base = (g .Γ.γ a +₊ g .Γ.γ δ) +₊
      ((ε -₊ (g .Γ.γ δ +₊ h .Γ.γ η) , Δ) +₊
        (h .Γ.γ η +₊ h .Γ.γ b))

    base+outer<ρ : fst (base +₊ outer) <ℚ fst ρ
    base+outer<ρ = begin<
      fst (base +₊ outer)
        ≡→≤⟨ cong (ℚ._+ fst outer)
          (threeBridge ε (g .Γ.γ δ) (h .Γ.γ η)
            (g .Γ.γ a) (h .Γ.γ b) Δ)
          ∙ sym (ℚ.+Assoc (fst ε)
            (fst (g .Γ.γ a +₊ h .Γ.γ b)) (fst outer)) ⟩
      fst ε ℚ.+ fst ((g .Γ.γ a +₊ h .Γ.γ b) +₊ outer)
        <⟨ +MonoL< _ _ (fst ε) tail<gap ⟩
      fst (ε +₊ gap)
        ≡→≤⟨ ℚ.+Comm (fst ε) (fst gap) ∙ minusPlus₊ ρ ε ⟩
      fst ρ ◾

    outer<ρ : outer <₊ ρ
    outer<ρ = begin<
      fst outer
        <⟨ <₊SumRight outer (g .Γ.γ a +₊ h .Γ.γ b) ⟩
      fst ((g .Γ.γ a +₊ h .Γ.γ b) +₊ outer)
        <⟨ tail<gap ⟩
      fst gap <⟨ Δ<₊ ρ ε ⟩
      fst ρ ◾

    Δouter : 0 ℚ.< ρ -₊ outer
    Δouter = <→0<Δ (fst outer) (fst ρ) outer<ρ

    target : ℚ₊
    target = (ρ -₊ outer , Δouter)

    base<target : base <₊ target
    base<target = +CancelR< (fst base) (fst target) (fst outer)
      (subst (fst (base +₊ outer) <ℚ_)
        (sym (minusPlus₊ ρ outer)) base+outer<ρ)

    combined : Slack (x a) (y b) base
    combined =
      slackTri (x a) (x δ) (y b)
        (g .Γ.γ a +₊ g .Γ.γ δ)
        ((ε -₊ (g .Γ.γ δ +₊ h .Γ.γ η) , Δ) +₊
          (h .Γ.γ η +₊ h .Γ.γ b))
        (xc a δ)
        (slackTri (x δ) (y η) (y b)
          (ε -₊ (g .Γ.γ δ +₊ h .Γ.γ η) , Δ)
          (h .Γ.γ η +₊ h .Γ.γ b)
          inner (yc η b))

    direct : x a S.∼̂ₛ[ target ] y b
    direct = combined target base<target


private
  fromTruncatedScaleRec : R.Recℭ̂ᵣ S.ℭ̂ₛ Slack
  fromTruncatedScaleRec .R.Recℭ̂ᵣ.ιA = S.ι
  fromTruncatedScaleRec .R.Recℭ̂ᵣ.limA = chooseGammaSeqLimit
  fromTruncatedScaleRec .R.Recℭ̂ᵣ.eqA = slackEq
  fromTruncatedScaleRec .R.Recℭ̂ᵣ.ι-ι-B x y ε x≈y δ ε<δ =
    S.ι-ι x y δ (PM.isMonotone≈< x y ε δ ε<δ x≈y)
  fromTruncatedScaleRec .R.Recℭ̂ᵣ.ι-lim-B = slackIotaLim
  fromTruncatedScaleRec .R.Recℭ̂ᵣ.lim-ι-B = slackLimIota
  fromTruncatedScaleRec .R.Recℭ̂ᵣ.lim-lim-B = slackLimLim
  fromTruncatedScaleRec .R.Recℭ̂ᵣ.isPropB = isPropSlack


fromTruncatedScale : R.ℭ̂ᵣ → S.ℭ̂ₛ
fromTruncatedScale = R.Recℭ̂ᵣ.go fromTruncatedScaleRec

fromTruncatedScaleSlack : ∀ x y ε →
  x R.∼̂ᵣ[ ε ] y → Slack (fromTruncatedScale x) (fromTruncatedScale y) ε
fromTruncatedScaleSlack x y ε = R.Recℭ̂ᵣ.go∼ fromTruncatedScaleRec

-- A single relation is preserved with an arbitrarily small radius loss.
-- Families of relations at every radius therefore map without loss.

fromTruncatedScaleAll∼ : ∀ x y →
  (∀ ε → x R.∼̂ᵣ[ ε ] y) →
  ∀ ε → fromTruncatedScale x S.∼̂ₛ[ ε ] fromTruncatedScale y
fromTruncatedScaleAll∼ x y close ε =
  fromTruncatedScaleSlack x y (ε /2₊) (close (ε /2₊)) ε (/2₊<id ε)

fromTruncatedScale-ι : ∀ x → fromTruncatedScale (R.ι x) ≡ S.ι x
fromTruncatedScale-ι = R.Recℭ̂ᵣ.β-go-ι fromTruncatedScaleRec

fromTruncatedScale-lim : ∀ x gx →
  fromTruncatedScale (R.lim x gx) ≡
    chooseGammaSeqLimit (fromTruncatedScale ∘ x)
      (R.Recℭ̂ᵣ.mapWitness fromTruncatedScaleRec gx)
fromTruncatedScale-lim = R.Recℭ̂ᵣ.β-go-lim fromTruncatedScaleRec


fromTruncatedScale-lim-canonical : ∀ x g xc →
  fromTruncatedScale (R.lim x ∣ g , xc ∣₁) ≡
    S.lim (Sample (fromTruncatedScale ∘ x) g)
      ∣ sampleCauchy (fromTruncatedScale ∘ x) g
          (λ ε δ → fromTruncatedScaleSlack (x ε) (x δ)
            (g .Γ.γ ε +₊ g .Γ.γ δ) (xc ε δ)) ∣₁
fromTruncatedScale-lim-canonical x g xc =
    fromTruncatedScale-lim x ∣ g , xc ∣₁
  ∙ chooseGammaSeqLimit-β (fromTruncatedScale ∘ x) g
      (λ ε δ → fromTruncatedScaleSlack (x ε) (x δ)
        (g .Γ.γ ε +₊ g .Γ.γ δ) (xc ε δ))


-- Public names for the sampling data used by the computation rule above.

dyadicRadius : ℕ → ℚ₊
dyadicRadius = dyadic

samplingModulus : ℚ₊ → ℕ
samplingModulus = modulus

sampleFamily : (ℚ₊ → S.ℭ̂ₛ) → Γ → ℕ → S.ℭ̂ₛ
sampleFamily = Sample

sampleFamilyCauchy : ∀ (x : ℚ₊ → S.ℭ̂ₛ) g
  → (∀ ε δ →
      Slack (x ε) (x δ) (g .Γ.γ ε +₊ g .Γ.γ δ))
  → S.CauchySeq (sampleFamily x g)
sampleFamilyCauchy = sampleCauchy

samplingModulus-small : ∀ ε →
  fst (dyadicRadius (samplingModulus ε)) <ℚ fst (ε /4₊)
samplingModulus-small = modulus-small
