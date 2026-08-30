open import Cubical.Foundations.Prelude
open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.CauchySequence.Extension.Lipschitz
  {ℓM ℓM' ℓN ℓN'}
  (M' : PremetricSpace ℓM ℓM')
  (N' : PremetricSpace ℓN ℓN') where

open import Cubical.Foundations.Function

open import Cubical.Algebra.Ring
open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Base as ℚ hiding (isProp∼)
open import Cubical.Data.Rationals.Inverse
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Rationals.Order as ℚ

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Relation.Premetric.Mappings

import Cubical.Relation.Premetric.Completion.CauchySequence.Base
  as CauchyCompletion
import Cubical.Relation.Premetric.Completion.CauchySequence.Premetric
  as CompletionPremetric

module S = CauchyCompletion M'
module SP = CompletionPremetric M'
module T = CauchyCompletion N'
module TP = CompletionPremetric N'

open PositiveRationals
open OrderedCommRingTheory ℚOrderedCommRing
open OrderedCommRingReasoning ℚOrderedCommRing

private
  M = M' .fst
  N = N' .fst
  module PTarget = PremetricStr (TP.CompletionPremetricSpace .snd)
  module ℚRing = RingTheory (OrderedCommRing→Ring ℚOrderedCommRing)

  scaleDifference : ∀ (L ε δ : ℚ₊) →
    fst L ℚ.· (fst ε ℚ.- fst δ) ≡
      (fst L ℚ.· fst ε) ℚ.- (fst L ℚ.· fst δ)
  scaleDifference L ε δ =
      ℚ.·DistL+ (fst L) (fst ε) (ℚ.- fst δ)
    ∙ cong (fst (L ·₊ ε) ℚ.+_) (ℚRing.-DistR· (fst L) (fst δ))

  scaleDifferenceSum : ∀ (L ε δ η : ℚ₊) →
    fst L ℚ.· (fst ε ℚ.- (fst δ ℚ.+ fst η)) ≡
      (fst L ℚ.· fst ε) ℚ.-
        ((fst L ℚ.· fst δ) ℚ.+ (fst L ℚ.· fst η))
  scaleDifferenceSum L ε δ η =
      scaleDifference L ε (δ +₊ η)
    ∙ cong (fst (L ·₊ ε) ℚ.+_)
        (cong ℚ.-_ (ℚ.·DistL+ (fst L) (fst δ) (fst η)))


module WithLipschitz
  (L : ℚ₊)
  (f : M → N)
  (f-lip : IsLipschitzWith (M' .snd) f (N' .snd) L) where

  mutual
    liftᴸ : S.Completion → T.Completion
    liftᴸ (S.ι x) = T.ι (f x)
    liftᴸ (S.lim x gx) =
      T.lim (liftᴸ ∘ x) (mapWitness gx)
    liftᴸ (S.eqCompletion x y x∼y i) =
      T.eqCompletion (liftᴸ x) (liftᴸ y)
        (λ ε → PTarget.subst≈ (liftᴸ x) (liftᴸ y)
          (·／ L ε) (liftᴸ-pres≈ᶜ (x∼y (ε ₊／₊ L)))) i

    liftᴸ-pres≈ᶜ : ∀ {x y ε} →
      x S.≈ᶜ[ ε ] y →
      liftᴸ x T.≈ᶜ[ L ·₊ ε ] liftᴸ y
    liftᴸ-pres≈ᶜ (S.ι-ι x y ε x≈y) =
      T.ι-ι (f x) (f y) (L ·₊ ε)
        (f-lip .IsLipschitzWith.pres≈ x y ε x≈y)
    liftᴸ-pres≈ᶜ (S.ι-lim x y gy N ε δ yc Δ r) =
      T.ι-lim (f x) (liftᴸ ∘ y) (mapWitness gy)
        N (L ·₊ ε) (L ·₊ δ)
        (λ m n N≤m N≤n → liftᴸ-pres≈ᶜ (yc m n N≤m N≤n))
        Δ' inner'
      where
      δ<ε : fst δ ℚ.< fst ε
      δ<ε = 0<Δ→< (fst δ) (fst ε) Δ

      Lδ<Lε : fst (L ·₊ δ) ℚ.< fst (L ·₊ ε)
      Lδ<Lε = ·MonoL< _ _ (fst L) (snd L) δ<ε

      Δ' : 0 ℚ.< (L ·₊ ε) -₊ (L ·₊ δ)
      Δ' = <→0<Δ _ _ Lδ<Lε

      inner' : T.ι (f x) T.≈ᶜ[
          ((L ·₊ ε) -₊ (L ·₊ δ) , Δ') ] liftᴸ (y N)
      inner' = PTarget.subst≈ (T.ι (f x)) (liftᴸ (y N))
        (scaleDifference L ε δ) (liftᴸ-pres≈ᶜ r)
    liftᴸ-pres≈ᶜ (S.lim-ι x gx N y ε δ xc Δ r) =
      T.lim-ι (liftᴸ ∘ x) (mapWitness gx)
        N (f y) (L ·₊ ε) (L ·₊ δ)
        (λ m n N≤m N≤n → liftᴸ-pres≈ᶜ (xc m n N≤m N≤n))
        Δ' inner'
      where
      δ<ε : fst δ ℚ.< fst ε
      δ<ε = 0<Δ→< (fst δ) (fst ε) Δ

      Lδ<Lε : fst (L ·₊ δ) ℚ.< fst (L ·₊ ε)
      Lδ<Lε = ·MonoL< _ _ (fst L) (snd L) δ<ε

      Δ' : 0 ℚ.< (L ·₊ ε) -₊ (L ·₊ δ)
      Δ' = <→0<Δ _ _ Lδ<Lε

      inner' : liftᴸ (x N) T.≈ᶜ[
          ((L ·₊ ε) -₊ (L ·₊ δ) , Δ') ] T.ι (f y)
      inner' = PTarget.subst≈ (liftᴸ (x N)) (T.ι (f y))
        (scaleDifference L ε δ) (liftᴸ-pres≈ᶜ r)
    liftᴸ-pres≈ᶜ
      (S.lim-lim x gx N y gy K ε δ η xc yc Δ r) =
      T.lim-lim (liftᴸ ∘ x) (mapWitness gx) N
        (liftᴸ ∘ y) (mapWitness gy) K
        (L ·₊ ε) (L ·₊ δ) (L ·₊ η)
        (λ m n N≤m N≤n → liftᴸ-pres≈ᶜ (xc m n N≤m N≤n))
        (λ m n K≤m K≤n → liftᴸ-pres≈ᶜ (yc m n K≤m K≤n))
        Δ' inner'
      where
      sum<ε : fst (δ +₊ η) ℚ.< fst ε
      sum<ε = 0<Δ→< _ _ Δ

      scaledSum<scaledε :
        fst ((L ·₊ δ) +₊ (L ·₊ η)) ℚ.< fst (L ·₊ ε)
      scaledSum<scaledε = begin<
        fst ((L ·₊ δ) +₊ (L ·₊ η))
          ≡→≤⟨ sym (ℚ.·DistL+ (fst L) (fst δ) (fst η)) ⟩
        fst (L ·₊ (δ +₊ η))
          <⟨ ·MonoL< _ _ (fst L) (snd L) sum<ε ⟩
        fst (L ·₊ ε) ◾

      Δ' : 0 ℚ.< (L ·₊ ε) -₊ ((L ·₊ δ) +₊ (L ·₊ η))
      Δ' = <→0<Δ _ _ scaledSum<scaledε

      inner' : liftᴸ (x N) T.≈ᶜ[
          ((L ·₊ ε) -₊ ((L ·₊ δ) +₊ (L ·₊ η)) , Δ')
        ] liftᴸ (y K)
      inner' = PTarget.subst≈ (liftᴸ (x N)) (liftᴸ (y K))
        (scaleDifferenceSum L ε δ η) (liftᴸ-pres≈ᶜ r)
    liftᴸ-pres≈ᶜ (S.isProp≈ᶜ x ε y p q i) =
      T.isProp≈ᶜ (liftᴸ x) (L ·₊ ε) (liftᴸ y)
        (liftᴸ-pres≈ᶜ p) (liftᴸ-pres≈ᶜ q) i

    mapWitness : ∀ {x} → S.IsCauchySequence x →
      T.IsCauchySequence (liftᴸ ∘ x)
    mapWitness gx ε = mapAtWitness ε (gx (ε ₊／₊ L))

    -- As for the nonexpanding recursor, both truncation constructors must
    -- remain visible to expose the structural recursive calls to Agda.
    mapAtWitness : ∀ {x} ε →
      ∥ S.CauchyTail x (ε ₊／₊ L) ∥₁ →
      ∥ T.CauchyTail (liftᴸ ∘ x) ε ∥₁
    mapAtWitness {x = x} ε ∣ N , xc ∣₁ =
      ∣ N , (λ m n N≤m N≤n →
        PTarget.subst≈ (liftᴸ (x m)) (liftᴸ (x n))
          (·／ L ε) (liftᴸ-pres≈ᶜ (xc m n N≤m N≤n))) ∣₁
    mapAtWitness ε (squash₁ p q i) =
      squash₁ (mapAtWitness ε p) (mapAtWitness ε q) i


  liftLipschitzWith :
    Σ[ F ∈ (S.Completion → T.Completion) ]
      IsLipschitzWith
        (SP.CompletionPremetricSpace .snd) F
        (TP.CompletionPremetricSpace .snd) L
  liftLipschitzWith .fst = liftᴸ
  liftLipschitzWith .snd .IsLipschitzWith.pres≈ x y ε =
    liftᴸ-pres≈ᶜ

  liftᴸ-ι : ∀ x → liftᴸ (S.ι x) ≡ T.ι (f x)
  liftᴸ-ι x = refl

  liftᴸ-lim : ∀ x gx →
    liftᴸ (S.lim x gx) ≡
    T.lim (liftᴸ ∘ x) (mapWitness gx)
  liftᴸ-lim x gx = refl


liftLipschitzWith : ∀ L (f : M → N) →
  IsLipschitzWith (M' .snd) f (N' .snd) L →
  Σ[ F ∈ (S.Completion → T.Completion) ]
    IsLipschitzWith
      (SP.CompletionPremetricSpace .snd) F
      (TP.CompletionPremetricSpace .snd) L
liftLipschitzWith = WithLipschitz.liftLipschitzWith

liftLipschitzWith-ι : ∀ L f f-lip x →
  fst (liftLipschitzWith L f f-lip) (S.ι x) ≡ T.ι (f x)
liftLipschitzWith-ι L f f-lip x = refl

liftLipschitzWith-lim : ∀ L f f-lip x gx →
  fst (liftLipschitzWith L f f-lip) (S.lim x gx) ≡
  T.lim (fst (liftLipschitzWith L f f-lip) ∘ x)
    (WithLipschitz.mapWitness L f f-lip gx)
liftLipschitzWith-lim L f f-lip x gx = refl
