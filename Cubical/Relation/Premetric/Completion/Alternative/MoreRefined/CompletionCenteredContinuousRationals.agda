module Cubical.Relation.Premetric.Completion.Alternative.MoreRefined.CompletionCenteredContinuousRationals where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Base as ℚ
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Rationals.Order as ℚ
  renaming (_<_ to _<ℚ_ ; _≤_ to _≤ℚ_)

open import Cubical.Relation.Premetric.Base
open import Cubical.Relation.Premetric.Mappings
open import Cubical.Relation.Premetric.Instances.Rationals

import Cubical.Relation.Premetric.Completion.Alternative.MoreRefined.Base
  as MoreRefinedDefinition
import Cubical.Relation.Premetric.Completion.Alternative.MoreRefined.Properties
  as MoreRefinedPropertiesDefinition

module S = MoreRefinedDefinition ℚPremetricSpace
module SP = MoreRefinedPropertiesDefinition ℚPremetricSpace

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ
open OrderedCommRingStr (snd ℚOrderedCommRing)
open OrderedCommRingTheory ℚOrderedCommRing
open OrderedCommRingReasoning ℚOrderedCommRing


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


-- The graph predicate also makes sense when the rational function already
-- takes values in the completion.

JointlyApproximableFor :
  (ℚ → S.ℭ̂ₛ) → S.ℭ̂ₛ → S.ℭ̂ₛ → Type₀
JointlyApproximableFor f x y = ∀ α β →
  ∃[ q ∈ ℚ ]
    (S.ι q S.∼̂ₛ[ α ] x) ×
    (f q S.∼̂ₛ[ β ] y)

isPropJointlyApproximableFor : ∀ f x y →
  isProp (JointlyApproximableFor f x y)
isPropJointlyApproximableFor f x y =
  isPropΠ2 λ _ _ → squash₁


-- This is epsilon-delta continuity at a point of the completed domain in
-- center-free form.  Rational points in the indicated open ball must have
-- images of small pairwise diameter.  A whole local modulus is bundled
-- before truncation; separately truncating each delta would require a
-- countable-choice principle when constructing an image Cauchy sequence.

record IsCompletionContinuousAtWith
  (f : ℚ → S.ℭ̂ₛ) (x : S.ℭ̂ₛ) (μ : ℚ₊ → ℚ₊) : Type₀ where
  no-eta-equality
  field
    pres∼ : ∀ q r ε →
      S.ι q S.∼̂ₛ[ μ ε ] x →
      S.ι r S.∼̂ₛ[ μ ε ] x →
      f q S.∼̂ₛ[ ε ] f r

open IsCompletionContinuousAtWith

record IsCompletionCenteredContinuous
  (f : ℚ → S.ℭ̂ₛ) : Type₀ where
  no-eta-equality
  field
    at : ∀ (x : S.ℭ̂ₛ) →
      ∃[ μ ∈ (ℚ₊ → ℚ₊) ] IsCompletionContinuousAtWith f x μ

open IsCompletionCenteredContinuous

-- The primitive limit relation has an injected left endpoint.  Density
-- upgrades the corresponding late-term lemma to an arbitrary completed
-- left endpoint.  The small radius is deliberately generous: it keeps the
-- proof structural and avoids rational normalization arithmetic.

close-lim-from-late : ∀ z y gy N yc ε n →
    N ((ε /4₊) /4₊) ℕ.≤ n →
    z S.∼̂ₛ[ (((ε /4₊) /4₊) /4₊) ] y n →
    z S.∼̂ₛ[ ε ] S.lim y gy
close-lim-from-late z y gy N yc ε n late z∼yn =
    PT.rec (S.isProp∼ z ε (S.lim y gy)) withApprox
      (SP.∃approx z small)
    where
    outer = ε /4₊
    required = outer /4₊
    small = required /4₊

    twiceSmall<required : (small +₊ small) <₊ required
    twiceSmall<required = begin<
      fst (small +₊ small)
        ≡→≤⟨ /4+/4≡/2 (fst required) ⟩
      fst (required /2₊)
        <⟨ /2₊<id required ⟩
      fst required ◾

    small<outer : small <₊ outer
    small<outer = ℚ.isTrans< _ _ _
      (/4₊<id required) (/4₊<id outer)

    smallPlusOuter<ε : (small +₊ outer) <₊ ε
    smallPlusOuter<ε = begin<
      fst (small +₊ outer)
        <⟨ +MonoR< (fst small) (fst outer) (fst outer)
             small<outer ⟩
      fst (outer +₊ outer)
        ≡→≤⟨ /4+/4≡/2 (fst ε) ⟩
      fst (ε /2₊)
        <⟨ /2₊<id ε ⟩
      fst ε ◾

    withApprox :
      (Σ[ q ∈ ℚ ] (S.ι q S.∼̂ₛ[ small ] z)) →
      z S.∼̂ₛ[ ε ] S.lim y gy
    withApprox (q , ιq∼z) =
      S.isMonotone∼̂ₛ< z (S.lim y gy)
        (small +₊ outer) ε smallPlusOuter<ε
        (S.tri∼ z (S.ι q) (S.lim y gy) small outer
          (S.sym∼ (S.ι q) z small ιq∼z)
          (SP.ι-close-lim-from-late q y gy N yc outer n late
            (S.isMonotone∼̂ₛ< (S.ι q) (y n)
              (small +₊ small) required twiceSmall<required
              (S.tri∼ (S.ι q) z (y n) small small
                ιq∼z z∼yn))))


jointlyApproximable-equal : ∀ (f : ℚ → S.ℭ̂ₛ) →
  IsCompletionCenteredContinuous f →
  ∀ x y y' →
  JointlyApproximableFor f x y →
  JointlyApproximableFor f x y' →
  y ≡ y'
jointlyApproximable-equal f f-cc x y y' xy xy' =
  PT.rec (S.isSetℭ̂ₛ y y') withLocalData (f-cc .at x)
  where
  withLocalData :
    (Σ[ μ ∈ (ℚ₊ → ℚ₊) ]
      IsCompletionContinuousAtWith f x μ) →
    y ≡ y'
  withLocalData (μ , local) = S.eqℭ y y' close
    where
    close : ∀ ε → y S.∼̂ₛ[ ε ] y'
    close ε = PT.rec2 (S.isProp∼ y ε y') step
      (xy (μ outputRadius) outputRadius)
      (xy' (μ outputRadius) outputRadius)
      where
      outputRadius = ε /4₊

      step :
        (Σ[ q ∈ ℚ ]
          (S.ι q S.∼̂ₛ[ μ outputRadius ] x) ×
          (f q S.∼̂ₛ[ outputRadius ] y)) →
        (Σ[ r ∈ ℚ ]
          (S.ι r S.∼̂ₛ[ μ outputRadius ] x) ×
          (f r S.∼̂ₛ[ outputRadius ] y')) →
        y S.∼̂ₛ[ ε ] y'
      step (q , ιq∼x , fq∼y) (r , ιr∼x , fr∼y') =
        S.isMonotone∼̂ₛ< y y' _ ε (tripleQuarter< ε)
          (S.tri∼ y (f r) y'
            (outputRadius +₊ outputRadius) outputRadius
            (S.tri∼ y (f q) (f r) outputRadius outputRadius
              (S.sym∼ (f q) y outputRadius fq∼y)
              (local .pres∼ q r outputRadius ιq∼x ιr∼x))
            fr∼y')


LiftFiber : (ℚ → S.ℭ̂ₛ) → S.ℭ̂ₛ → Type₀
LiftFiber f x = Σ[ y ∈ S.ℭ̂ₛ ] JointlyApproximableFor f x y

isPropLiftFiber : ∀ (f : ℚ → S.ℭ̂ₛ) →
  IsCompletionCenteredContinuous f →
  ∀ x → isProp (LiftFiber f x)
isPropLiftFiber f f-cc x (y , xy) (y' , xy') =
  Σ≡Prop (isPropJointlyApproximableFor f x)
    (jointlyApproximable-equal f f-cc x y y' xy xy')


private
  baseFiber : ∀ f q → LiftFiber f (S.ι q)
  baseFiber f q .fst = f q
  baseFiber f q .snd α β =
    ∣ q , S.isRefl∼̂ₛ (S.ι q) α
        , S.isRefl∼̂ₛ (f q) β ∣₁


  imageCauchySeq : ∀ f x gx y μ →
    IsCompletionContinuousAtWith f (S.lim x gx) μ →
    (∀ n → JointlyApproximableFor f (x n) (y n)) →
    S.CauchySeq x → S.CauchySeq y
  imageCauchySeq f x gx y μ local joint (N , xc) .fst ε =
    N (μ (ε /4₊) /4₊)
  imageCauchySeq f x gx y μ local joint (N , xc) .snd
    ε m n Nε≤m Nε≤n =
    PT.rec2 (S.isProp∼ (y m) ε (y n)) step
      (joint m sourceRadius outputRadius)
      (joint n sourceRadius outputRadius)
    where
    outputRadius = ε /4₊
    centerRadius = μ outputRadius
    sourceRadius = centerRadius /4₊

    step :
      (Σ[ q ∈ ℚ ]
        (S.ι q S.∼̂ₛ[ sourceRadius ] x m) ×
        (f q S.∼̂ₛ[ outputRadius ] y m)) →
      (Σ[ r ∈ ℚ ]
        (S.ι r S.∼̂ₛ[ sourceRadius ] x n) ×
        (f r S.∼̂ₛ[ outputRadius ] y n)) →
      y m S.∼̂ₛ[ ε ] y n
    step (q , ιq∼xm , fq∼ym) (r , ιr∼xn , fr∼yn) =
      S.isMonotone∼̂ₛ< (y m) (y n) _ ε (tripleQuarter< ε)
        (S.tri∼ (y m) (f r) (y n)
          (outputRadius +₊ outputRadius) outputRadius
          (S.tri∼ (y m) (f q) (f r) outputRadius outputRadius
            (S.sym∼ (f q) (y m) outputRadius fq∼ym)
            (local .pres∼ q r outputRadius ιq∼center ιr∼center))
          fr∼yn)
      where
      ιq∼center : S.ι q S.∼̂ₛ[ centerRadius ] S.lim x gx
      ιq∼center = SP.ι-close-lim-from-late
        q x gx N xc centerRadius m Nε≤m ιq∼xm

      ιr∼center : S.ι r S.∼̂ₛ[ centerRadius ] S.lim x gx
      ιr∼center = SP.ι-close-lim-from-late
        r x gx N xc centerRadius n Nε≤n ιr∼xn


  imageSeqWitness : ∀ f x gx y μ →
    IsCompletionContinuousAtWith f (S.lim x gx) μ →
    (∀ n → JointlyApproximableFor f (x n) (y n)) →
    S.SeqWitness y
  imageSeqWitness f x gx y μ local joint =
    PT.map (imageCauchySeq f x gx y μ local joint) gx


  limitJointlyApproximable : ∀ f x gx y μ
    (local : IsCompletionContinuousAtWith f (S.lim x gx) μ)
    (joint : ∀ n → JointlyApproximableFor f (x n) (y n)) →
    JointlyApproximableFor f
      (S.lim x gx)
      (S.lim y (imageSeqWitness f x gx y μ local joint))
  limitJointlyApproximable f x gx y μ local joint α β =
    PT.rec squash₁ withCauchy gx
    where
    gy = imageSeqWitness f x gx y μ local joint

    withCauchy : S.CauchySeq x →
      ∃[ q ∈ ℚ ]
        (S.ι q S.∼̂ₛ[ α ] S.lim x gx) ×
        (f q S.∼̂ₛ[ β ] S.lim y gy)
    withCauchy sourceCauchy@(N , xc) =
      PT.map makeLateApproximation
        (joint n (α /4₊) targetSmall)
      where
      targetCauchy : S.CauchySeq y
      targetCauchy =
        imageCauchySeq f x gx y μ local joint sourceCauchy

      K : ℚ₊ → ℕ
      K = targetCauchy .fst

      yc : ∀ ε m n → K ε ℕ.≤ m → K ε ℕ.≤ n →
        y m S.∼̂ₛ[ ε ] y n
      yc = targetCauchy .snd

      targetRequired = (β /4₊) /4₊
      targetSmall = targetRequired /4₊

      n : ℕ
      n = ℕ.max (N (α /4₊)) (K targetRequired)

      makeLateApproximation :
        (Σ[ q ∈ ℚ ]
          (S.ι q S.∼̂ₛ[ α /4₊ ] x n) ×
          (f q S.∼̂ₛ[ targetSmall ] y n)) →
        Σ[ q ∈ ℚ ]
          (S.ι q S.∼̂ₛ[ α ] S.lim x gx) ×
          (f q S.∼̂ₛ[ β ] S.lim y gy)
      makeLateApproximation (q , ιq∼xn , fq∼yn) = q ,
        SP.ι-close-lim-from-late q x gx N xc α n
          (ℕ.left-≤-max
            {m = N (α /4₊)} {n = K targetRequired}) ιq∼xn ,
        close-lim-from-late (f q) y gy K yc β n
          (ℕ.right-≤-max
            {n = K targetRequired} {m = N (α /4₊)}) fq∼yn


  limitFiberWithData :
    ∀ (f : ℚ → S.ℭ̂ₛ)
      (f-cc : IsCompletionCenteredContinuous f)
      (x : ℕ → S.ℭ̂ₛ) (gx : S.SeqWitness x) →
    (∀ n → LiftFiber f (x n)) →
    (Σ[ μ ∈ (ℚ₊ → ℚ₊) ]
      IsCompletionContinuousAtWith f (S.lim x gx) μ) →
    LiftFiber f (S.lim x gx)
  limitFiberWithData f f-cc x gx IH (μ , local) =
    S.lim y gy , limitJointlyApproximable f x gx y μ local joint
    where
    y : ℕ → S.ℭ̂ₛ
    y n = IH n .fst

    joint : ∀ n → JointlyApproximableFor f (x n) (y n)
    joint n = IH n .snd

    gy : S.SeqWitness y
    gy = imageSeqWitness f x gx y μ local joint


  limitFiber :
    ∀ (f : ℚ → S.ℭ̂ₛ)
      (f-cc : IsCompletionCenteredContinuous f)
      (x : ℕ → S.ℭ̂ₛ) (gx : S.SeqWitness x) →
    (∀ n → LiftFiber f (x n)) →
    LiftFiber f (S.lim x gx)
  limitFiber f f-cc x gx IH =
    PT.rec (isPropLiftFiber f f-cc (S.lim x gx))
      (limitFiberWithData f f-cc x gx IH)
      (f-cc .at (S.lim x gx))


  fiberElim :
    ∀ (f : ℚ → S.ℭ̂ₛ)
      (f-cc : IsCompletionCenteredContinuous f) →
    S.Elimℭ̂ₛ-Prop (LiftFiber f)
  fiberElim f f-cc .S.Elimℭ̂ₛ-Prop.ιA = baseFiber f
  fiberElim f f-cc .S.Elimℭ̂ₛ-Prop.limA = limitFiber f f-cc
  fiberElim f f-cc .S.Elimℭ̂ₛ-Prop.isPropA =
    isPropLiftFiber f f-cc


liftFiber : ∀ (f : ℚ → S.ℭ̂ₛ) →
  IsCompletionCenteredContinuous f →
  ∀ x → LiftFiber f x
liftFiber f f-cc = S.Elimℭ̂ₛ-Prop.go (fiberElim f f-cc)

liftCompletionCenteredContinuous :
  (f : ℚ → S.ℭ̂ₛ) →
  IsCompletionCenteredContinuous f →
  S.ℭ̂ₛ → S.ℭ̂ₛ
liftCompletionCenteredContinuous f f-cc x =
  liftFiber f f-cc x .fst

liftCompletionCenteredContinuous-joint :
  ∀ (f : ℚ → S.ℭ̂ₛ) (f-cc : IsCompletionCenteredContinuous f) x →
  JointlyApproximableFor f x
    (liftCompletionCenteredContinuous f f-cc x)
liftCompletionCenteredContinuous-joint f f-cc x =
  liftFiber f f-cc x .snd

liftCompletionCenteredContinuous-ι :
  ∀ (f : ℚ → S.ℭ̂ₛ) (f-cc : IsCompletionCenteredContinuous f) q →
  liftCompletionCenteredContinuous f f-cc (S.ι q) ≡ f q
liftCompletionCenteredContinuous-ι f f-cc q = refl


liftCompletionCenteredContinuous-unique :
  ∀ (f : ℚ → S.ℭ̂ₛ) (f-cc : IsCompletionCenteredContinuous f)
    (G : S.ℭ̂ₛ → S.ℭ̂ₛ) →
    (∀ x → JointlyApproximableFor f x (G x)) →
    liftCompletionCenteredContinuous f f-cc ≡ G
liftCompletionCenteredContinuous-unique f f-cc G G-joint =
  funExt λ x → jointlyApproximable-equal f f-cc x _ _
    (liftCompletionCenteredContinuous-joint f f-cc x)
    (G-joint x)

liftCompletionCenteredContinuous-hypothesis-independent :
  ∀ (f : ℚ → S.ℭ̂ₛ)
    (f-cc f-cc' : IsCompletionCenteredContinuous f) →
    liftCompletionCenteredContinuous f f-cc ≡
      liftCompletionCenteredContinuous f f-cc'
liftCompletionCenteredContinuous-hypothesis-independent
  f f-cc f-cc' =
  liftCompletionCenteredContinuous-unique f f-cc
    (liftCompletionCenteredContinuous f f-cc')
    (liftCompletionCenteredContinuous-joint f f-cc')


liftCompletionCenteredContinuous-isContinuous : ∀ (f : ℚ → S.ℭ̂ₛ)
  (f-cc : IsCompletionCenteredContinuous f) →
  isContinuous
    (SP.ℭ̂ₛPremetricSpace .snd)
    (liftCompletionCenteredContinuous f f-cc)
    (SP.ℭ̂ₛPremetricSpace .snd)
liftCompletionCenteredContinuous-isContinuous f f-cc x
  .IsContinuousAt.pres≈ ε =
  PT.map withLocalData (f-cc .at x)
  where
  F = liftCompletionCenteredContinuous f f-cc

  withLocalData :
    (Σ[ μ ∈ (ℚ₊ → ℚ₊) ]
      IsCompletionContinuousAtWith f x μ) →
    Σ[ δ ∈ ℚ₊ ]
      (∀ y → x S.∼̂ₛ[ δ ] y → F x S.∼̂ₛ[ ε ] F y)
  withLocalData (μ , local) = sourceRadius , preserve
    where
    outputRadius = ε /4₊
    centerRadius = μ outputRadius
    sourceRadius = centerRadius /4₊

    source<Center : sourceRadius <₊ centerRadius
    source<Center = /4₊<id centerRadius

    twiceSource<Center : (sourceRadius +₊ sourceRadius) <₊ centerRadius
    twiceSource<Center = begin<
      fst (sourceRadius +₊ sourceRadius)
        ≡→≤⟨ /4+/4≡/2 (fst centerRadius) ⟩
      fst (centerRadius /2₊)
        <⟨ /2₊<id centerRadius ⟩
      fst centerRadius ◾

    preserve : ∀ y →
      x S.∼̂ₛ[ sourceRadius ] y →
      F x S.∼̂ₛ[ ε ] F y
    preserve y x∼y =
      PT.rec2 (S.isProp∼ (F x) ε (F y)) step
        (liftCompletionCenteredContinuous-joint f f-cc x
          sourceRadius outputRadius)
        (liftCompletionCenteredContinuous-joint f f-cc y
          sourceRadius outputRadius)
      where
      step :
        (Σ[ q ∈ ℚ ]
          (S.ι q S.∼̂ₛ[ sourceRadius ] x) ×
          (f q S.∼̂ₛ[ outputRadius ] F x)) →
        (Σ[ r ∈ ℚ ]
          (S.ι r S.∼̂ₛ[ sourceRadius ] y) ×
          (f r S.∼̂ₛ[ outputRadius ] F y)) →
        F x S.∼̂ₛ[ ε ] F y
      step (q , ιq∼x , fq∼Fx) (r , ιr∼y , fr∼Fy) =
        S.isMonotone∼̂ₛ< (F x) (F y) _ ε (tripleQuarter< ε)
          (S.tri∼ (F x) (f r) (F y)
            (outputRadius +₊ outputRadius) outputRadius
            (S.tri∼ (F x) (f q) (f r)
              outputRadius outputRadius
              (S.sym∼ (f q) (F x) outputRadius fq∼Fx)
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
