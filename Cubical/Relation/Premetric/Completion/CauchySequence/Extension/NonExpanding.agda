open import Cubical.Foundations.Prelude
open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.CauchySequence.Extension.NonExpanding
  {ℓM ℓM' ℓN ℓN'}
  (M' : PremetricSpace ℓM ℓM')
  (N' : PremetricSpace ℓN ℓN') where

open import Cubical.Foundations.Function

open import Cubical.Data.Rationals.Base hiding (isProp∼)
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Relation.Premetric.Mappings
open CategoryStructures

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ

import Cubical.Relation.Premetric.Completion.CauchySequence.Base
  as CauchyCompletion
import Cubical.Relation.Premetric.Completion.CauchySequence.Premetric
  as CompletionPremetric

module S = CauchyCompletion M'
module SP = CompletionPremetric M'
module T = CauchyCompletion N'
module TP = CompletionPremetric N'


module WithNonExpanding
  (f : M' .fst → N' .fst)
  (f-ne : IsNonExpanding (M' .snd) f (N' .snd)) where

  mutual
    liftⁿ : S.Completion → T.Completion
    liftⁿ (S.ι x) = T.ι (f x)
    liftⁿ (S.lim x gx) =
      T.lim (liftⁿ ∘ x) (mapWitness gx)
    liftⁿ (S.eqCompletion x y x∼y i) =
      T.eqCompletion (liftⁿ x) (liftⁿ y)
        (λ ε → liftⁿ-pres≈ᶜ (x∼y ε)) i

    liftⁿ-pres≈ᶜ : ∀ {x y ε} →
      x S.≈ᶜ[ ε ] y →
      liftⁿ x T.≈ᶜ[ ε ] liftⁿ y
    liftⁿ-pres≈ᶜ (S.ι-ι x y ε x≈y) =
      T.ι-ι (f x) (f y) ε
        (f-ne .IsNonExpanding.pres≈ x y ε x≈y)
    liftⁿ-pres≈ᶜ (S.ι-lim x y gy N ε δ yc Δ r) =
      T.ι-lim (f x) (liftⁿ ∘ y) (mapWitness gy)
        N ε δ
        (λ m n N≤m N≤n →
          liftⁿ-pres≈ᶜ (yc m n N≤m N≤n))
        Δ (liftⁿ-pres≈ᶜ r)
    liftⁿ-pres≈ᶜ (S.lim-ι x gx N y ε δ xc Δ r) =
      T.lim-ι (liftⁿ ∘ x) (mapWitness gx)
        N (f y) ε δ
        (λ m n N≤m N≤n →
          liftⁿ-pres≈ᶜ (xc m n N≤m N≤n))
        Δ (liftⁿ-pres≈ᶜ r)
    liftⁿ-pres≈ᶜ
      (S.lim-lim x gx N y gy K ε δ η xc yc Δ r) =
      T.lim-lim (liftⁿ ∘ x) (mapWitness gx) N
        (liftⁿ ∘ y) (mapWitness gy) K ε δ η
        (λ m n N≤m N≤n →
          liftⁿ-pres≈ᶜ (xc m n N≤m N≤n))
        (λ m n K≤m K≤n →
          liftⁿ-pres≈ᶜ (yc m n K≤m K≤n))
        Δ (liftⁿ-pres≈ᶜ r)
    liftⁿ-pres≈ᶜ (S.isProp≈ᶜ x ε y p q i) =
      T.isProp≈ᶜ (liftⁿ x) ε (liftⁿ y)
        (liftⁿ-pres≈ᶜ p) (liftⁿ-pres≈ᶜ q) i

    mapWitness : ∀ {x} → S.IsCauchySequence x →
      T.IsCauchySequence (liftⁿ ∘ x)
    mapWitness gx ε = mapAtWitness (gx ε)

    -- Keeping both constructors visible is essential for termination
    -- checking.  Replacing these clauses by PT.map obscures the structural
    -- descent from the checker.
    mapAtWitness : ∀ {x ε} →
      ∥ S.CauchyTail x ε ∥₁ →
      ∥ T.CauchyTail (liftⁿ ∘ x) ε ∥₁
    mapAtWitness ∣ N , xc ∣₁ =
      ∣ N , (λ m n N≤m N≤n →
        liftⁿ-pres≈ᶜ (xc m n N≤m N≤n)) ∣₁
    mapAtWitness (squash₁ p q i) =
      squash₁ (mapAtWitness p) (mapAtWitness q) i


  liftNonExpanding :
    NE[ SP.CompletionPremetricSpace , TP.CompletionPremetricSpace ]
  liftNonExpanding .fst = liftⁿ
  liftNonExpanding .snd .IsNonExpanding.pres≈ x y ε =
    liftⁿ-pres≈ᶜ

  liftⁿ-ι : ∀ x → liftⁿ (S.ι x) ≡ T.ι (f x)
  liftⁿ-ι x = refl

  liftⁿ-lim : ∀ x gx →
    liftⁿ (S.lim x gx) ≡
    T.lim (liftⁿ ∘ x) (mapWitness gx)
  liftⁿ-lim x gx = refl


liftNonExpanding :
  NE[ M' , N' ] →
  NE[ SP.CompletionPremetricSpace , TP.CompletionPremetricSpace ]
liftNonExpanding f =
  WithNonExpanding.liftNonExpanding (fst f) (snd f)

liftNonExpanding-ι : ∀ (f : NE[ M' , N' ]) x →
  fst (liftNonExpanding f) (S.ι x) ≡ T.ι (fst f x)
liftNonExpanding-ι f x = refl

liftNonExpanding-lim : ∀ (f : NE[ M' , N' ]) x gx →
  fst (liftNonExpanding f) (S.lim x gx) ≡
  T.lim (fst (liftNonExpanding f) ∘ x)
    (WithNonExpanding.mapWitness (fst f) (snd f) gx)
liftNonExpanding-lim f x gx = refl


-- Density makes nonexpanding extensions unique even when the codomain is a
-- a different Cauchy-sequence completion.

nonExpandingExtensionality :
  ∀ (F G : NE[ SP.CompletionPremetricSpace , TP.CompletionPremetricSpace ]) →
  fst F ∘ S.ι ≡ fst G ∘ S.ι → F ≡ G
nonExpandingExtensionality F G agree = NE≡ (funExt equalAt)
  where
  closeAt : ∀ x ε → fst F x T.≈ᶜ[ ε ] fst G x
  closeAt x ε =
    PT.rec (T.isProp≈ᶜ (fst F x) ε (fst G x)) close
      (SP.∃approx x (ε /2₊))
    where
    close :
      (Σ[ q ∈ (M' .fst) ]
        (S.ι q S.≈ᶜ[ ε /2₊ ] x)) →
      fst F x T.≈ᶜ[ ε ] fst G x
    close (q , ιq∼x) =
      subst (fst F x T.≈ᶜ[_] fst G x)
        (ℚ₊≡ (/2+/2≡id (fst ε)))
        (TP.tri≈ᶜ (fst F x) (fst G (S.ι q)) (fst G x)
          (ε /2₊) (ε /2₊)
          (subst (fst F x T.≈ᶜ[ ε /2₊ ]_)
            (funExt⁻ agree q)
            (F .snd .IsNonExpanding.pres≈
              x (S.ι q) (ε /2₊)
              (S.sym≈ᶜ (S.ι q) x (ε /2₊) ιq∼x)))
          (G .snd .IsNonExpanding.pres≈
            (S.ι q) x (ε /2₊) ιq∼x))

  equalAt : ∀ x → fst F x ≡ fst G x
  equalAt x = T.eqCompletion (fst F x) (fst G x) (closeAt x)
