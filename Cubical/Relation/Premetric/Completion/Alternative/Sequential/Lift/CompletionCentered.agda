open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.Alternative.Sequential.Lift.CompletionCentered
  {ℓM} {ℓM'} {ℓN} {ℓN'}
  (M' : PremetricSpace ℓM ℓM')
  (N' : PremetricSpace ℓN ℓN') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Base hiding (isProp∼)
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Rationals.Order as ℚ
  renaming (_<_ to _<ℚ_ ; _≤_ to _≤ℚ_)

open import Cubical.Relation.Premetric.Mappings

import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Base
  as SequentialDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Properties
  as SequentialPropertiesDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Lift.CauchyContinuous
  as CauchyContinuousDefinition

module S = SequentialDefinition M'
module SP = SequentialPropertiesDefinition M'
module T = SequentialDefinition N'
module TP = SequentialPropertiesDefinition N'
module C = CauchyContinuousDefinition M' N'

private
  M = M' .fst
  ℓₘ = ℓ-max (ℓ-max ℓM ℓM') (ℓ-max ℓN ℓN')

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ
open OrderedCommRingStr (snd ℚOrderedCommRing)
open OrderedCommRingTheory ℚOrderedCommRing
open OrderedCommRingReasoning ℚOrderedCommRing


-- A whole local modulus is bundled before truncation.  This is stronger
-- data than ordinary pointwise continuity, whose radius is truncated
-- separately for each output radius.

record IsCompletionContinuousAtWith
  (f : M → T.ℭ̂ₛ) (x : S.ℭ̂ₛ) (μ : ℚ₊ → ℚ₊) : Type ℓₘ where
  no-eta-equality
  field
    pres∼ : ∀ q r ε →
      S.ι q S.∼̂ₛ[ μ ε ] x →
      S.ι r S.∼̂ₛ[ μ ε ] x →
      f q T.∼̂ₛ[ ε ] f r

open IsCompletionContinuousAtWith

record IsCompletionCenteredContinuous
  (f : M → T.ℭ̂ₛ) : Type ℓₘ where
  no-eta-equality
  field
    at : ∀ (x : S.ℭ̂ₛ) →
      ∃[ μ ∈ (ℚ₊ → ℚ₊) ] IsCompletionContinuousAtWith f x μ

open IsCompletionCenteredContinuous


private
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


  imageCauchySeq : ∀ f x gx y μ →
    IsCompletionContinuousAtWith f (S.lim x gx) μ →
    (∀ n → C.JointlyApproximableFor f (x n) (y n)) →
    S.CauchySeq x → T.CauchySeq y
  imageCauchySeq f x gx y μ local joint (N , xc) .fst ε =
    N (μ (ε /4₊) /4₊)
  imageCauchySeq f x gx y μ local joint (N , xc) .snd
    ε m n Nε≤m Nε≤n =
    PT.rec2 (T.isProp∼ (y m) ε (y n)) step
      (joint m sourceRadius outputRadius)
      (joint n sourceRadius outputRadius)
    where
    outputRadius = ε /4₊
    centerRadius = μ outputRadius
    sourceRadius = centerRadius /4₊

    step :
      (Σ[ q ∈ M ]
        (S.ι q S.∼̂ₛ[ sourceRadius ] x m) ×
        (f q T.∼̂ₛ[ outputRadius ] y m)) →
      (Σ[ r ∈ M ]
        (S.ι r S.∼̂ₛ[ sourceRadius ] x n) ×
        (f r T.∼̂ₛ[ outputRadius ] y n)) →
      y m T.∼̂ₛ[ ε ] y n
    step (q , ιq∼xm , fq∼ym) (r , ιr∼xn , fr∼yn) =
      T.isMonotone∼̂ₛ< (y m) (y n) _ ε (tripleQuarter< ε)
        (T.tri∼ (y m) (f r) (y n)
          (outputRadius +₊ outputRadius) outputRadius
          (T.tri∼ (y m) (f q) (f r) outputRadius outputRadius
            (T.sym∼ (f q) (y m) outputRadius fq∼ym)
            (local .pres∼ q r outputRadius ιq∼center ιr∼center))
          fr∼yn)
      where
      ιq∼center : S.ι q S.∼̂ₛ[ centerRadius ] S.lim x gx
      ιq∼center = SP.ι-close-lim-from-late
        q x gx N xc centerRadius m Nε≤m ιq∼xm

      ιr∼center : S.ι r S.∼̂ₛ[ centerRadius ] S.lim x gx
      ιr∼center = SP.ι-close-lim-from-late
        r x gx N xc centerRadius n Nε≤n ιr∼xn


-- The completion-centered hypothesis is a sufficient source of the newer,
-- stronger graph-Cauchy lifting interface.  All extension construction and
-- uniqueness results are therefore inherited from that interface.

completionCenteredContinuous→cauchyContinuous :
  ∀ {f : M → T.ℭ̂ₛ} →
  IsCompletionCenteredContinuous f → C.IsCauchyContinuous f
completionCenteredContinuous→cauchyContinuous {f} f-cc =
  C.cauchyContinuous preserve
  where
  preserve : ∀ x y →
    (∀ n → C.JointlyApproximableFor f (x n) (y n)) →
    S.SeqWitness x → T.SeqWitness y
  preserve x y joint gx =
    PT.rec squash₁ withLocalData (f-cc .at (S.lim x gx))
    where
    withLocalData :
      (Σ[ μ ∈ (ℚ₊ → ℚ₊) ]
        IsCompletionContinuousAtWith f (S.lim x gx) μ) →
      T.SeqWitness y
    withLocalData (μ , local) =
      PT.map (imageCauchySeq f x gx y μ local joint) gx


liftCompletionCenteredContinuous :
  (f : M → T.ℭ̂ₛ) →
  IsCompletionCenteredContinuous f →
  S.ℭ̂ₛ → T.ℭ̂ₛ
liftCompletionCenteredContinuous f f-cc =
  C.liftCauchyContinuous f
    (completionCenteredContinuous→cauchyContinuous f-cc)

liftCompletionCenteredContinuous-joint :
  ∀ (f : M → T.ℭ̂ₛ) (f-cc : IsCompletionCenteredContinuous f) x →
  C.JointlyApproximableFor f x
    (liftCompletionCenteredContinuous f f-cc x)
liftCompletionCenteredContinuous-joint f f-cc =
  C.liftCauchyContinuous-joint f
    (completionCenteredContinuous→cauchyContinuous f-cc)

liftCompletionCenteredContinuous-ι :
  ∀ (f : M → T.ℭ̂ₛ) (f-cc : IsCompletionCenteredContinuous f) q →
  liftCompletionCenteredContinuous f f-cc (S.ι q) ≡ f q
liftCompletionCenteredContinuous-ι f f-cc =
  C.liftCauchyContinuous-ι f
    (completionCenteredContinuous→cauchyContinuous f-cc)

liftCompletionCenteredContinuous-unique :
  ∀ (f : M → T.ℭ̂ₛ) (f-cc : IsCompletionCenteredContinuous f)
    (G : S.ℭ̂ₛ → T.ℭ̂ₛ) →
    (∀ x → C.JointlyApproximableFor f x (G x)) →
    liftCompletionCenteredContinuous f f-cc ≡ G
liftCompletionCenteredContinuous-unique f f-cc =
  C.liftCauchyContinuous-unique f
    (completionCenteredContinuous→cauchyContinuous f-cc)

liftCompletionCenteredContinuous-hypothesis-independent :
  ∀ (f : M → T.ℭ̂ₛ)
    (f-cc f-cc' : IsCompletionCenteredContinuous f) →
    liftCompletionCenteredContinuous f f-cc ≡
      liftCompletionCenteredContinuous f f-cc'
liftCompletionCenteredContinuous-hypothesis-independent f f-cc f-cc' =
  C.liftCauchyContinuous-hypothesis-independent f
    (completionCenteredContinuous→cauchyContinuous f-cc)
    (completionCenteredContinuous→cauchyContinuous f-cc')

liftCompletionCenteredContinuous-ext :
  ∀ (f g : M → T.ℭ̂ₛ)
    (f-cc : IsCompletionCenteredContinuous f)
    (g-cc : IsCompletionCenteredContinuous g) →
  (∀ q → f q ≡ g q) →
  liftCompletionCenteredContinuous f f-cc ≡
    liftCompletionCenteredContinuous g g-cc
liftCompletionCenteredContinuous-ext f g f-cc g-cc f∼g =
  C.liftCauchyContinuous-ext f g
    (completionCenteredContinuous→cauchyContinuous f-cc)
    (completionCenteredContinuous→cauchyContinuous g-cc)
    f∼g


liftCompletionCenteredContinuous-isContinuous : ∀ (f : M → T.ℭ̂ₛ)
  (f-cc : IsCompletionCenteredContinuous f) →
  isContinuous
    (SP.ℭ̂ₛPremetricSpace .snd)
    (liftCompletionCenteredContinuous f f-cc)
    (TP.ℭ̂ₛPremetricSpace .snd)
liftCompletionCenteredContinuous-isContinuous f f-cc x
  .IsContinuousAt.pres≈ ε =
  PT.map withLocalData (f-cc .at x)
  where
  F = liftCompletionCenteredContinuous f f-cc

  withLocalData :
    (Σ[ μ ∈ (ℚ₊ → ℚ₊) ]
      IsCompletionContinuousAtWith f x μ) →
    Σ[ δ ∈ ℚ₊ ]
      (∀ y → x S.∼̂ₛ[ δ ] y → F x T.∼̂ₛ[ ε ] F y)
  withLocalData (μ , local) = inputRadius ε , preserve ε
    where
    inputRadius : ℚ₊ → ℚ₊
    inputRadius ε = μ (ε /4₊) /4₊

    preserve : ∀ ε y →
      x S.∼̂ₛ[ inputRadius ε ] y →
      F x T.∼̂ₛ[ ε ] F y
    preserve ε y x∼y =
      PT.rec2 (T.isProp∼ (F x) ε (F y)) step
        (liftCompletionCenteredContinuous-joint f f-cc x
          sourceRadius outputRadius)
        (liftCompletionCenteredContinuous-joint f f-cc y
          sourceRadius outputRadius)
      where
      outputRadius = ε /4₊
      centerRadius = μ outputRadius
      sourceRadius = centerRadius /4₊

      source<Center : sourceRadius <₊ centerRadius
      source<Center = /4₊<id centerRadius

      twiceSource<Center :
        (sourceRadius +₊ sourceRadius) <₊ centerRadius
      twiceSource<Center = begin<
        fst (sourceRadius +₊ sourceRadius)
          ≡→≤⟨ /4+/4≡/2 (fst centerRadius) ⟩
        fst (centerRadius /2₊)
          <⟨ /2₊<id centerRadius ⟩
        fst centerRadius ◾

      step :
        (Σ[ q ∈ M ]
          (S.ι q S.∼̂ₛ[ sourceRadius ] x) ×
          (f q T.∼̂ₛ[ outputRadius ] F x)) →
        (Σ[ r ∈ M ]
          (S.ι r S.∼̂ₛ[ sourceRadius ] y) ×
          (f r T.∼̂ₛ[ outputRadius ] F y)) →
        F x T.∼̂ₛ[ ε ] F y
      step (q , ιq∼x , fq∼Fx) (r , ιr∼y , fr∼Fy) =
        T.isMonotone∼̂ₛ< (F x) (F y) _ ε (tripleQuarter< ε)
          (T.tri∼ (F x) (f r) (F y)
            (outputRadius +₊ outputRadius) outputRadius
            (T.tri∼ (F x) (f q) (f r)
              outputRadius outputRadius
              (T.sym∼ (f q) (F x) outputRadius fq∼Fx)
              (local .pres∼ q r outputRadius
                (S.isMonotone∼̂ₛ< (S.ι q) x
                  sourceRadius centerRadius source<Center ιq∼x)
                (S.isMonotone∼̂ₛ< (S.ι r) x
                  (sourceRadius +₊ sourceRadius) centerRadius
                  twiceSource<Center
                  (S.tri∼ (S.ι r) y x sourceRadius sourceRadius
                    ιr∼y
                    (S.sym∼ x y sourceRadius x∼y)))))
            fr∼Fy)
