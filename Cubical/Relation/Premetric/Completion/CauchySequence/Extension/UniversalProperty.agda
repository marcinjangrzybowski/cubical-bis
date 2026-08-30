open import Cubical.Foundations.Prelude hiding (lift)
open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.CauchySequence.Extension.UniversalProperty
  {ℓM ℓM' ℓN ℓN'}
  (M' : PremetricSpace ℓM ℓM')
  (N' : PremetricSpace ℓN ℓN') where

open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Rationals.Base as ℚ hiding (isProp∼)
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Relation.Premetric.Mappings
open CategoryStructures
open import Cubical.Relation.Premetric.Properties

open import Cubical.Tactics.CommRingSolver.Specialised.Rationals

import Cubical.Relation.Premetric.Completion.CauchySequence.Base
  as CauchyCompletion
import Cubical.Relation.Premetric.Completion.CauchySequence.Premetric
  as CompletionPremetric
import Cubical.Relation.Premetric.Completion.CauchySequence.Limits
  as CauchySequenceLimits

module S = CauchyCompletion M'
module SP = CompletionPremetric M'
module PN = PremetricStr (N' .snd)
module N = PremetricTheory N'
module L = CauchySequenceLimits N'

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ
open OrderedCommRingStr (snd ℚOrderedCommRing)
open OrderedCommRingReasoning ℚOrderedCommRing
open OrderedCommRingTheory ℚOrderedCommRing


module WithCauchySequenceLimits
  (complete : L.HasCauchySequenceLimits)
  (f : M' .fst → N' .fst)
  (f-ne : IsNonExpanding (M' .snd) f (N' .snd)) where

  private
    -- A term close to one tail value is close to the selected limit.  The
    -- strict unused radius pays for convergence of a sufficiently late term.
    close-limit-from-tail :
      ∀ (x : ℕ → N' .fst) (gx : L.IsCauchySequence x)
        (K : ℕ) (ε δ ρ : ℚ₊) →
      (ρ +₊ δ <₊ ε) →
      (∀ m n → K ℕ.≤ m → K ℕ.≤ n →
        x m PN.≈[ δ ] x n) →
      ∀ u → u PN.≈[ ρ ] x K →
      u PN.≈[ ε ] fst (complete x gx)
    close-limit-from-tail x gx K ε δ ρ used<ε xc u u≈xK =
      PT.rec (PN.isProp≈ u (fst (complete x gx)) ε)
        withLimit (complete x gx .snd small)
      where
      used : ℚ₊
      used = ρ +₊ δ

      gap : ℚ₊
      gap = [ ε -₊ used ]⟨ used<ε ⟩

      small : ℚ₊
      small = gap /2₊

      total : ℚ₊
      total = ρ +₊ (δ +₊ small)

      total<ε : total <₊ ε
      total<ε = begin<
        fst total
          ≡→≤⟨ ℚ.+Assoc (fst ρ) (fst δ) (fst small) ⟩
        fst (used +₊ small)
          <⟨ +MonoL< (fst small) (fst gap) (fst used)
               (/2₊<id gap) ⟩
        fst (used +₊ gap)
          ≡→≤⟨ ℚ.+Comm (fst used) (fst gap)
               ∙ minusPlus₊ ε used ⟩
        fst ε ◾

      withLimit :
        Σ[ L ∈ ℕ ]
          (∀ n → L ℕ.≤ n →
            x n PN.≈[ small ] fst (complete x gx)) →
        u PN.≈[ ε ] fst (complete x gx)
      withLimit (L , late≈limit) =
        PN.isMonotone≈< u (fst (complete x gx))
          total ε total<ε
          (PN.isTriangular≈ u (x K) (fst (complete x gx))
            ρ (δ +₊ small) u≈xK
            (PN.isTriangular≈ (x K) (x n)
              (fst (complete x gx)) δ small
              (xc K n ℕ.≤-refl K≤n)
              (late≈limit n L≤n)))
        where
        n : ℕ
        n = ℕ.max K L

        K≤n : K ℕ.≤ n
        K≤n = ℕ.left-≤-max {m = K} {n = L}

        L≤n : L ℕ.≤ n
        L≤n = ℕ.right-≤-max {n = L} {m = K}

    close-limits-from-tails :
      ∀ (x y : ℕ → N' .fst)
        (gx : L.IsCauchySequence x)
        (gy : L.IsCauchySequence y)
        (K L : ℕ) (ε δ η ρ : ℚ₊) →
      (ρ +₊ (δ +₊ η) <₊ ε) →
      (∀ m n → K ℕ.≤ m → K ℕ.≤ n →
        x m PN.≈[ δ ] x n) →
      (∀ m n → L ℕ.≤ m → L ℕ.≤ n →
        y m PN.≈[ η ] y n) →
      x K PN.≈[ ρ ] y L →
      fst (complete x gx) PN.≈[ ε ] fst (complete y gy)
    close-limits-from-tails
        x y gx gy K L ε δ η ρ used<ε xc yc xK≈yL =
      PN.isSym≈ _ _ ε
        (close-limit-from-tail x gx K ε δ σ
          σ+δ<ε xc (fst (complete y gy))
          (PN.isSym≈ _ _ σ xK≈limy))
      where
      used : ℚ₊
      used = ρ +₊ (δ +₊ η)

      gap : ℚ₊
      gap = [ ε -₊ used ]⟨ used<ε ⟩

      halfGap : ℚ₊
      halfGap = gap /2₊

      σ : ℚ₊
      σ = ρ +₊ (η +₊ halfGap)

      ρ+η<σ : ρ +₊ η <₊ σ
      ρ+η<σ = begin<
        fst (ρ +₊ η)
          <⟨ <₊SumLeft (ρ +₊ η) halfGap ⟩
        fst ((ρ +₊ η) +₊ halfGap)
          ≡→≤⟨ sym (ℚ.+Assoc (fst ρ) (fst η) (fst halfGap)) ⟩
        fst σ ◾

      σ+δ<ε : σ +₊ δ <₊ ε
      σ+δ<ε = begin<
        fst (σ +₊ δ)
          ≡→≤⟨ ℚ! ⟩
        fst (used +₊ halfGap)
          <⟨ +MonoL< (fst halfGap) (fst gap) (fst used)
               (/2₊<id gap) ⟩
        fst (used +₊ gap)
          ≡→≤⟨ ℚ.+Comm (fst used) (fst gap)
               ∙ minusPlus₊ ε used ⟩
        fst ε ◾

      xK≈limy : x K PN.≈[ σ ] fst (complete y gy)
      xK≈limy =
        close-limit-from-tail y gy L σ η ρ
          ρ+η<σ yc (x K) xK≈yL


  mutual
    lift : S.Completion → N' .fst
    lift (S.ι x) = f x
    lift (S.lim x gx) =
      fst (complete (lift ∘ x) (mapWitness gx))
    lift (S.eqCompletion x y x∼y i) =
      PN.isSeparated≈ (lift x) (lift y)
        (λ ε → lift-pres≈ᶜ (x∼y ε)) i

    lift-pres≈ᶜ : ∀ {x y ε} →
      x S.≈ᶜ[ ε ] y → lift x PN.≈[ ε ] lift y
    lift-pres≈ᶜ (S.ι-ι x y ε x≈y) =
      f-ne .IsNonExpanding.pres≈ x y ε x≈y
    lift-pres≈ᶜ (S.ι-lim x y gy K ε δ yc Δ inner) =
      PT.rec (PN.isProp≈ (f x) (lift (S.lim y gy)) ε)
        useRounded (PN.isRounded≈ _ _ _ (lift-pres≈ᶜ inner))
      where
      residual : ℚ₊
      residual = (ε -₊ δ , Δ)

      useRounded :
        Σ[ ρ ∈ ℚ₊ ]
          (ρ <₊ residual) ×
          (f x PN.≈[ ρ ] lift (y K)) →
        f x PN.≈[ ε ] lift (S.lim y gy)
      useRounded (ρ , ρ<residual , close) =
        close-limit-from-tail (lift ∘ y) (mapWitness gy)
          K ε δ ρ budget
          (λ m n K≤m K≤n →
            lift-pres≈ᶜ (yc m n K≤m K≤n))
          (f x) close
        where
        budget : ρ +₊ δ <₊ ε
        budget = begin<
          fst (ρ +₊ δ)
            <⟨ +MonoR< (fst ρ) (fst residual) (fst δ)
                 ρ<residual ⟩
          fst (residual +₊ δ)
            ≡→≤⟨ minusPlus₊ ε δ ⟩
          fst ε ◾
    lift-pres≈ᶜ (S.lim-ι x gx K y ε δ xc Δ inner) =
      PN.isSym≈ _ _ ε
        (PT.rec (PN.isProp≈ (f y) (lift (S.lim x gx)) ε)
          useRounded
          (PN.isRounded≈ _ _ _
            (PN.isSym≈ _ _ _ (lift-pres≈ᶜ inner))))
      where
      residual : ℚ₊
      residual = (ε -₊ δ , Δ)

      useRounded :
        Σ[ ρ ∈ ℚ₊ ]
          (ρ <₊ residual) ×
          (f y PN.≈[ ρ ] lift (x K)) →
        f y PN.≈[ ε ] lift (S.lim x gx)
      useRounded (ρ , ρ<residual , close) =
        close-limit-from-tail (lift ∘ x) (mapWitness gx)
          K ε δ ρ budget
          (λ m n K≤m K≤n →
            lift-pres≈ᶜ (xc m n K≤m K≤n))
          (f y) close
        where
        budget : ρ +₊ δ <₊ ε
        budget = begin<
          fst (ρ +₊ δ)
            <⟨ +MonoR< (fst ρ) (fst residual) (fst δ)
                 ρ<residual ⟩
          fst (residual +₊ δ)
            ≡→≤⟨ minusPlus₊ ε δ ⟩
          fst ε ◾
    lift-pres≈ᶜ
        (S.lim-lim x gx K y gy L ε δ η xc yc Δ inner) =
      PT.rec (PN.isProp≈ (lift (S.lim x gx))
        (lift (S.lim y gy)) ε)
        useRounded (PN.isRounded≈ _ _ _ (lift-pres≈ᶜ inner))
      where
      tails : ℚ₊
      tails = δ +₊ η

      residual : ℚ₊
      residual = (ε -₊ tails , Δ)

      useRounded :
        Σ[ ρ ∈ ℚ₊ ]
          (ρ <₊ residual) ×
          (lift (x K) PN.≈[ ρ ] lift (y L)) →
        lift (S.lim x gx) PN.≈[ ε ] lift (S.lim y gy)
      useRounded (ρ , ρ<residual , close) =
        close-limits-from-tails
          (lift ∘ x) (lift ∘ y)
          (mapWitness gx) (mapWitness gy)
          K L ε δ η ρ budget
          (λ m n K≤m K≤n →
            lift-pres≈ᶜ (xc m n K≤m K≤n))
          (λ m n L≤m L≤n →
            lift-pres≈ᶜ (yc m n L≤m L≤n))
          close
        where
        budget : ρ +₊ (δ +₊ η) <₊ ε
        budget = begin<
          fst (ρ +₊ tails)
            <⟨ +MonoR< (fst ρ) (fst residual) (fst tails)
                 ρ<residual ⟩
          fst (residual +₊ tails)
            ≡→≤⟨ minusPlus₊ ε tails ⟩
          fst ε ◾
    lift-pres≈ᶜ (S.isProp≈ᶜ x ε y p q i) =
      PN.isProp≈ (lift x) (lift y) ε
        (lift-pres≈ᶜ p) (lift-pres≈ᶜ q) i

    mapWitness : ∀ {x} → S.IsCauchySequence x →
      L.IsCauchySequence (lift ∘ x)
    mapWitness gx ε = mapAtWitness (gx ε)

    -- As in the completion-valued lift, exposing both truncation
    -- constructors is necessary for Agda to see the recursive calls on the
    -- tail relations as structurally smaller.
    mapAtWitness : ∀ {x ε} →
      ∥ S.CauchyTail x ε ∥₁ →
      ∥ Σ[ K ∈ ℕ ]
          (∀ m n → K ℕ.≤ m → K ℕ.≤ n →
            lift (x m) PN.≈[ ε ] lift (x n)) ∥₁
    mapAtWitness ∣ K , xc ∣₁ =
      ∣ K , (λ m n K≤m K≤n →
        lift-pres≈ᶜ (xc m n K≤m K≤n)) ∣₁
    mapAtWitness (squash₁ p q i) =
      squash₁ (mapAtWitness p) (mapAtWitness q) i


  liftNonExpanding : NE[ SP.CompletionPremetricSpace , N' ]
  liftNonExpanding .fst = lift
  liftNonExpanding .snd .IsNonExpanding.pres≈ _ _ _ = lift-pres≈ᶜ

  lift-ι : ∀ x → lift (S.ι x) ≡ f x
  lift-ι x = refl

  lift-lim : ∀ x gx →
    lift (S.lim x gx) ≡
      fst (complete (lift ∘ x) (mapWitness gx))
  lift-lim x gx = refl


liftNonExpanding :
  L.HasCauchySequenceLimits →
  NE[ M' , N' ] →
  NE[ SP.CompletionPremetricSpace , N' ]
liftNonExpanding complete f =
  WithCauchySequenceLimits.liftNonExpanding
    complete (fst f) (snd f)

liftNonExpanding-ι :
  ∀ (complete : L.HasCauchySequenceLimits)
    (f : NE[ M' , N' ]) x →
  fst (liftNonExpanding complete f) (S.ι x) ≡ fst f x
liftNonExpanding-ι complete f x = refl


-- Quantitative density makes the extension unique in every separated
-- target; completeness is only needed to construct it.

nonExpandingExtensionality :
  ∀ (F G : NE[ SP.CompletionPremetricSpace , N' ]) →
  fst F ∘ S.ι ≡ fst G ∘ S.ι → F ≡ G
nonExpandingExtensionality F G agree = NE≡ (funExt equalAt)
  where
  closeAt : ∀ x ε → fst F x PN.≈[ ε ] fst G x
  closeAt x ε =
    PT.rec (PN.isProp≈ (fst F x) (fst G x) ε) close
      (SP.∃approx x (ε /2₊))
    where
    close :
      (Σ[ q ∈ (M' .fst) ]
        (S.ι q S.≈ᶜ[ ε /2₊ ] x)) →
      fst F x PN.≈[ ε ] fst G x
    close (q , ιq∼x) =
      subst (fst F x PN.≈[_] fst G x)
        (ℚ₊≡ (/2+/2≡id (fst ε)))
        (PN.isTriangular≈
          (fst F x) (fst G (S.ι q)) (fst G x)
          (ε /2₊) (ε /2₊)
          (subst (fst F x PN.≈[ ε /2₊ ]_)
            (funExt⁻ agree q)
            (F .snd .IsNonExpanding.pres≈
              x (S.ι q) (ε /2₊)
              (S.sym≈ᶜ (S.ι q) x (ε /2₊) ιq∼x)))
          (G .snd .IsNonExpanding.pres≈
            (S.ι q) x (ε /2₊) ιq∼x))

  equalAt : ∀ x → fst F x ≡ fst G x
  equalAt x = PN.isSeparated≈ (fst F x) (fst G x) (closeAt x)


-- Restriction along the dense injection is inverse to the lift.  This is
-- the mapping-space form of the nonexpanding universal property for the
-- recent, radiuswise notion of sequential completeness.

restrictNonExpanding :
  NE[ SP.CompletionPremetricSpace , N' ] → NE[ M' , N' ]
restrictNonExpanding F .fst = fst F ∘ S.ι
restrictNonExpanding F .snd .IsNonExpanding.pres≈ x y ε x≈y =
  F .snd .IsNonExpanding.pres≈ (S.ι x) (S.ι y) ε
    (S.ι-ι x y ε x≈y)


nonExpandingExtensionIso :
  L.HasCauchySequenceLimits →
  Iso NE[ M' , N' ] NE[ SP.CompletionPremetricSpace , N' ]
nonExpandingExtensionIso complete .Iso.fun =
  liftNonExpanding complete
nonExpandingExtensionIso complete .Iso.inv =
  restrictNonExpanding
nonExpandingExtensionIso complete .Iso.ret f =
  NE≡ (funExt (liftNonExpanding-ι complete f))
nonExpandingExtensionIso complete .Iso.sec F =
  nonExpandingExtensionality
    (liftNonExpanding complete (restrictNonExpanding F)) F
    (funExt (liftNonExpanding-ι complete
      (restrictNonExpanding F)))


nonExpandingExtensionEquiv :
  L.HasCauchySequenceLimits →
  NE[ M' , N' ] ≃ NE[ SP.CompletionPremetricSpace , N' ]
nonExpandingExtensionEquiv complete =
  isoToEquiv (nonExpandingExtensionIso complete)
