open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.Alternative.Sequential.Lift.PointwiseCompletionCentered
  {ℓM} {ℓM'} {ℓN} {ℓN'}
  (M' : PremetricSpace ℓM ℓM')
  (N' : PremetricSpace ℓN ℓN') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma
open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order as ℕ

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
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Lift.CompletionCentered
  as CompletionCenteredDefinition

module S = SequentialDefinition M'
module SP = SequentialPropertiesDefinition M'
module T = SequentialDefinition N'
module TP = SequentialPropertiesDefinition N'
module C = CauchyContinuousDefinition M' N'
module Bundled = CompletionCenteredDefinition M' N'

private
  M = M' .fst
  ℓₘ = ℓ-max (ℓ-max ℓM ℓM') (ℓ-max ℓN ℓN')
  ℓₜ = ℓ-max ℓN ℓN'

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ
open OrderedCommRingStr (snd ℚOrderedCommRing)
open OrderedCommRingTheory ℚOrderedCommRing
open OrderedCommRingReasoning ℚOrderedCommRing


-- This is the completion-centered condition with the same Π/truncation
-- order as ordinary pointwise continuity: the radius is chosen separately
-- (and merely) for each output epsilon.

CenteredRadiusFor :
  (M → T.ℭ̂ₛ) → S.ℭ̂ₛ → ℚ₊ → Type ℓₘ
CenteredRadiusFor f x ε =
  Σ[ δ ∈ ℚ₊ ]
    (∀ q r →
      S.ι q S.∼̂ₛ[ δ ] x →
      S.ι r S.∼̂ₛ[ δ ] x →
      f q T.∼̂ₛ[ ε ] f r)


record IsPointwiseCompletionCenteredContinuous
  (f : M → T.ℭ̂ₛ) : Type ℓₘ where
  no-eta-equality
  field
    at : ∀ x ε → ∥ CenteredRadiusFor f x ε ∥₁

open IsPointwiseCompletionCenteredContinuous


isPropIsPointwiseCompletionCenteredContinuous : ∀ f →
  isProp (IsPointwiseCompletionCenteredContinuous f)
isPropIsPointwiseCompletionCenteredContinuous f a b i .at x ε =
  squash₁ (a .at x ε) (b .at x ε) i


bundled→pointwise : ∀ {f} →
  Bundled.IsCompletionCenteredContinuous f →
  IsPointwiseCompletionCenteredContinuous f
bundled→pointwise {f} bundled .at x ε =
  PT.map atEpsilon
    (bundled .Bundled.IsCompletionCenteredContinuous.at x)
  where
  atEpsilon :
    (Σ[ μ ∈ (ℚ₊ → ℚ₊) ]
      Bundled.IsCompletionContinuousAtWith f x μ) →
    CenteredRadiusFor f x ε
  atEpsilon (μ , local) =
    μ ε , λ q r →
      local .Bundled.IsCompletionContinuousAtWith.pres∼ q r ε


-- Restricting an ordinarily continuous map to the dense base gives exactly
-- the pointwise centered condition, without commuting truncation with Π.

continuous→pointwiseRestriction :
  ∀ (F : S.ℭ̂ₛ → T.ℭ̂ₛ) →
  isContinuous
    (SP.ℭ̂ₛPremetricSpace .snd) F
    (TP.ℭ̂ₛPremetricSpace .snd) →
  IsPointwiseCompletionCenteredContinuous (F ∘ S.ι)
continuous→pointwiseRestriction F F-cont .at x ε =
  PT.map withRadius
    (F-cont x .IsContinuousAt.pres≈ (ε /2₊))
  where
  withRadius :
    (Σ[ δ ∈ ℚ₊ ]
      (∀ y → x S.∼̂ₛ[ δ ] y →
        F x T.∼̂ₛ[ ε /2₊ ] F y)) →
    CenteredRadiusFor (F ∘ S.ι) x ε
  withRadius (δ , preserve) = δ , λ q r ιq∼x ιr∼x →
    subst (F (S.ι q) T.∼̂ₛ[_] F (S.ι r))
      (ℚ₊≡ (/2+/2≡id (fst ε)))
      (T.tri∼ (F (S.ι q)) (F x) (F (S.ι r))
        (ε /2₊) (ε /2₊)
        (T.sym∼ (F x) (F (S.ι q)) (ε /2₊)
          (preserve (S.ι q)
            (S.sym∼ (S.ι q) x δ ιq∼x)))
        (preserve (S.ι r)
          (S.sym∼ (S.ι r) x δ ιr∼x)))


private
  tripleQuarter< : ∀ ε →
    ((ε /4₊ +₊ ε /4₊) +₊ ε /4₊) <₊ ε
  tripleQuarter< ε = begin<
    fst ((ε /4₊ +₊ ε /4₊) +₊ ε /4₊)
      ≡→≤⟨ cong (ℚ._+ fst (ε /4₊)) (/4+/4≡/2 (fst ε)) ⟩
    fst (ε /2₊ +₊ ε /4₊)
      <⟨ +MonoL< (fst (ε /4₊)) (fst (ε /2₊))
           (fst (ε /2₊)) (/4₊</2₊ ε) ⟩
    fst (ε /2₊ +₊ ε /2₊)
      ≡→≤⟨ /2+/2≡id (fst ε) ⟩
    fst ε ◾


-- Any total jointly-approximable graph is ordinarily continuous when its
-- rational restriction is pointwise completion-centered.  Each epsilon
-- eliminates only its own truncated radius, so no countable-choice step
-- occurs.

jointlyApproximableExtension-isContinuous :
  ∀ (f : M → T.ℭ̂ₛ) (F : S.ℭ̂ₛ → T.ℭ̂ₛ) →
  IsPointwiseCompletionCenteredContinuous f →
  (∀ x → C.JointlyApproximableFor f x (F x)) →
  isContinuous
    (SP.ℭ̂ₛPremetricSpace .snd)
    F
    (TP.ℭ̂ₛPremetricSpace .snd)
jointlyApproximableExtension-isContinuous f F pointwise joint x
  .IsContinuousAt.pres≈ ε =
  PT.map withRadius (pointwise .at x (ε /4₊))
  where
  withRadius :
    CenteredRadiusFor f x (ε /4₊) →
    Σ[ δ ∈ ℚ₊ ]
      (∀ y → x S.∼̂ₛ[ δ ] y → F x T.∼̂ₛ[ ε ] F y)
  withRadius (centerRadius , local) =
    sourceRadius , preserve
    where
    outputRadius = ε /4₊
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

    preserve : ∀ y →
      x S.∼̂ₛ[ sourceRadius ] y →
      F x T.∼̂ₛ[ ε ] F y
    preserve y x∼y =
      PT.rec2 (T.isProp∼ (F x) ε (F y)) step
        (joint x sourceRadius outputRadius)
        (joint y sourceRadius outputRadius)
      where
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
              (local q r
                (S.isMonotone∼̂ₛ< (S.ι q) x
                  sourceRadius centerRadius source<Center ιq∼x)
                (S.isMonotone∼̂ₛ< (S.ι r) x
                  (sourceRadius +₊ sourceRadius) centerRadius
                  twiceSource<Center
                  (S.tri∼ (S.ι r) y x sourceRadius sourceRadius
                    ιr∼y
                    (S.sym∼ x y sourceRadius x∼y)))))
            fr∼Fy)


-- Graph/Cauchy continuity is one way to supply a total graph and hence a
-- canonical lift.  Pointwise centeredness then gives its continuity.

liftCauchyContinuous-isContinuous :
  ∀ (f : M → T.ℭ̂ₛ) (f-cauchy : C.IsCauchyContinuous f) →
  IsPointwiseCompletionCenteredContinuous f →
  isContinuous
    (SP.ℭ̂ₛPremetricSpace .snd)
    (C.liftCauchyContinuous f f-cauchy)
    (TP.ℭ̂ₛPremetricSpace .snd)
liftCauchyContinuous-isContinuous f f-cauchy pointwise =
  jointlyApproximableExtension-isContinuous f
    (C.liftCauchyContinuous f f-cauchy)
    pointwise
    (C.liftCauchyContinuous-joint f f-cauchy)


-- For a graph-Cauchy restriction, the new pointwise condition is therefore
-- equivalent to ordinary continuity of its canonical lift.

pointwiseCentered≃continuousLift :
  ∀ (f : M → T.ℭ̂ₛ) (f-cauchy : C.IsCauchyContinuous f) →
  IsPointwiseCompletionCenteredContinuous f ≃
  isContinuous
    (SP.ℭ̂ₛPremetricSpace .snd)
    (C.liftCauchyContinuous f f-cauchy)
    (TP.ℭ̂ₛPremetricSpace .snd)
pointwiseCentered≃continuousLift f f-cauchy =
  propBiimpl→Equiv
    (isPropIsPointwiseCompletionCenteredContinuous f)
    (isPropIsContinuous
      (SP.ℭ̂ₛPremetricSpace .snd)
      (C.liftCauchyContinuous f f-cauchy)
      (TP.ℭ̂ₛPremetricSpace .snd))
    (liftCauchyContinuous-isContinuous f f-cauchy)
    (λ F-cont →
      subst IsPointwiseCompletionCenteredContinuous
        (funExt (C.liftCauchyContinuous-ι f f-cauchy))
        (continuous→pointwiseRestriction
          (C.liftCauchyContinuous f f-cauchy) F-cont))


-- Direct lifting attempt
-- ----------------------
--
-- Pointwise centeredness does prove the image graph Cauchy separately at
-- every epsilon.  The sequential completion constructor, however, asks for
-- one truncated Cauchy modulus containing all those choices at once.

CauchyTailAt : (ℕ → T.ℭ̂ₛ) → ℚ₊ → Type ℓₜ
CauchyTailAt y ε =
  Σ[ k ∈ ℕ ]
    (∀ m n → k ℕ.≤ m → k ℕ.≤ n → y m T.∼̂ₛ[ ε ] y n)


PointwiseSeqWitness : (ℕ → T.ℭ̂ₛ) → Type ℓₜ
PointwiseSeqWitness y = ∀ ε → ∥ CauchyTailAt y ε ∥₁


seqWitness→pointwiseSeqWitness : ∀ {y} →
  T.SeqWitness y → PointwiseSeqWitness y
seqWitness→pointwiseSeqWitness gy ε =
  PT.map
    (λ (K , yc) → K ε , yc ε)
    gy


BundledCauchyTails : (ℕ → T.ℭ̂ₛ) → Type ℓₜ
BundledCauchyTails y =
  ∥ ((ε : ℚ₊) → CauchyTailAt y ε) ∥₁


-- A completion `SeqWitness` contains exactly a simultaneously selected
-- family of the epsilon-wise tails; the difference is only packaging.

bundledCauchyTails≃seqWitness : ∀ y →
  BundledCauchyTails y ≃ T.SeqWitness y
bundledCauchyTails≃seqWitness y =
  propBiimpl→Equiv squash₁ squash₁ toWitness fromWitness
  where
  toWitness : BundledCauchyTails y → T.SeqWitness y
  toWitness = PT.map λ tails →
    (λ ε → fst (tails ε)) ,
    (λ ε → snd (tails ε))

  fromWitness : T.SeqWitness y → BundledCauchyTails y
  fromWitness = PT.map λ (K , yc) ε → K ε , yc ε


pointwiseCentered-presPointwiseCauchyGraph :
  ∀ {f : M → T.ℭ̂ₛ} →
  IsPointwiseCompletionCenteredContinuous f →
  ∀ x y →
  (∀ n → C.JointlyApproximableFor f (x n) (y n)) →
  S.SeqWitness x → PointwiseSeqWitness y
pointwiseCentered-presPointwiseCauchyGraph
  {f} pointwise x y joint gx ε =
  PT.rec squash₁ withRadius
    (pointwise .at (S.lim x gx) outputRadius)
  where
  outputRadius = ε /4₊

  withRadius :
    CenteredRadiusFor f (S.lim x gx) outputRadius →
    ∥ CauchyTailAt y ε ∥₁
  withRadius (centerRadius , local) =
    PT.map withSource gx
    where
    sourceRadius = centerRadius /4₊

    step :
      (N : ℚ₊ → ℕ) →
      (∀ θ m n → N θ ℕ.≤ m → N θ ℕ.≤ n →
        x m S.∼̂ₛ[ θ ] x n) →
      ∀ m n → N sourceRadius ℕ.≤ m → N sourceRadius ℕ.≤ n →
      (Σ[ q ∈ M ]
        (S.ι q S.∼̂ₛ[ sourceRadius ] x m) ×
        (f q T.∼̂ₛ[ outputRadius ] y m)) →
      (Σ[ r ∈ M ]
        (S.ι r S.∼̂ₛ[ sourceRadius ] x n) ×
        (f r T.∼̂ₛ[ outputRadius ] y n)) →
      y m T.∼̂ₛ[ ε ] y n

    withSource : S.CauchySeq x → CauchyTailAt y ε
    withSource (N , xc) =
      N sourceRadius , λ m n Nε≤m Nε≤n →
        PT.rec2 (T.isProp∼ (y m) ε (y n))
          (step N xc m n Nε≤m Nε≤n)
          (joint m sourceRadius outputRadius)
          (joint n sourceRadius outputRadius)

    step N xc m n Nε≤m Nε≤n
      (q , ιq∼xm , fq∼ym) (r , ιr∼xn , fr∼yn) =
      T.isMonotone∼̂ₛ< (y m) (y n) _ ε (tripleQuarter< ε)
        (T.tri∼ (y m) (f r) (y n)
          (outputRadius +₊ outputRadius) outputRadius
          (T.tri∼ (y m) (f q) (f r)
            outputRadius outputRadius
            (T.sym∼ (f q) (y m) outputRadius fq∼ym)
            (local q r ιq∼center ιr∼center))
          fr∼yn)
      where
      ιq∼center : S.ι q S.∼̂ₛ[ centerRadius ] S.lim x gx
      ιq∼center = SP.ι-close-lim-from-late
        q x gx N xc centerRadius m Nε≤m ιq∼xm

      ιr∼center : S.ι r S.∼̂ₛ[ centerRadius ] S.lim x gx
      ιr∼center = SP.ι-close-lim-from-late
        r x gx N xc centerRadius n Nε≤n ιr∼xn


-- This is the exact missing Π/truncation commute, restricted to the Cauchy
-- tail families needed by the target completion.

GraphPointwiseCauchyChoiceFor :
  (M → T.ℭ̂ₛ) → Type ℓₘ
GraphPointwiseCauchyChoiceFor f =
  ∀ x y →
  (∀ n → C.JointlyApproximableFor f (x n) (y n)) →
  S.SeqWitness x →
  PointwiseSeqWitness y →
  T.SeqWitness y


isPropGraphPointwiseCauchyChoiceFor : ∀ f →
  isProp (GraphPointwiseCauchyChoiceFor f)
isPropGraphPointwiseCauchyChoiceFor f =
  isPropΠ2 λ _ _ →
    isPropΠ λ _ →
    isPropΠ λ _ →
    isPropΠ λ _ → squash₁


cauchyContinuous→graphPointwiseCauchyChoice :
  ∀ {f : M → T.ℭ̂ₛ} →
  C.IsCauchyContinuous f →
  GraphPointwiseCauchyChoiceFor f
cauchyContinuous→graphPointwiseCauchyChoice cauchy
  x y joint gx _ =
  cauchy .C.IsCauchyContinuous.presCauchyGraph x y joint gx


pointwiseCentered→cauchyContinuousWithGraphChoice :
  ∀ {f : M → T.ℭ̂ₛ} →
  IsPointwiseCompletionCenteredContinuous f →
  GraphPointwiseCauchyChoiceFor f →
  C.IsCauchyContinuous f
pointwiseCentered→cauchyContinuousWithGraphChoice pointwise choice =
  C.cauchyContinuous λ x y joint gx →
    choice x y joint gx
      (pointwiseCentered-presPointwiseCauchyGraph
        pointwise x y joint gx)


-- For a fixed pointwise-centered map, this graph-specific choice is not just
-- sufficient for the current lifting route: it is equivalent to the exact
-- graph-Cauchy interface consumed by that route.

graphPointwiseCauchyChoice≃cauchyContinuous :
  ∀ {f : M → T.ℭ̂ₛ} →
  IsPointwiseCompletionCenteredContinuous f →
  GraphPointwiseCauchyChoiceFor f ≃ C.IsCauchyContinuous f
graphPointwiseCauchyChoice≃cauchyContinuous {f} pointwise =
  propBiimpl→Equiv
    (isPropGraphPointwiseCauchyChoiceFor f)
    (C.isPropIsCauchyContinuous f)
    (pointwiseCentered→cauchyContinuousWithGraphChoice pointwise)
    cauchyContinuous→graphPointwiseCauchyChoice


PointwiseCauchyChoice : Type ℓₜ
PointwiseCauchyChoice =
  ∀ y → PointwiseSeqWitness y → T.SeqWitness y


CauchyTailΠChoice : Type ℓₜ
CauchyTailΠChoice =
  ∀ y →
  (∀ ε → ∥ CauchyTailAt y ε ∥₁) →
  ∥ ((ε : ℚ₊) → CauchyTailAt y ε) ∥₁


cauchyTailΠChoice→pointwiseCauchyChoice :
  CauchyTailΠChoice → PointwiseCauchyChoice
cauchyTailΠChoice→pointwiseCauchyChoice choice y pointwise =
  equivFun (bundledCauchyTails≃seqWitness y)
    (choice y pointwise)


pointwiseCauchyChoice→cauchyTailΠChoice :
  PointwiseCauchyChoice → CauchyTailΠChoice
pointwiseCauchyChoice→cauchyTailΠChoice choice y pointwise =
  invEq (bundledCauchyTails≃seqWitness y)
    (choice y pointwise)


isPropPointwiseCauchyChoice : isProp PointwiseCauchyChoice
isPropPointwiseCauchyChoice =
  isPropΠ λ _ → isPropΠ λ _ → squash₁


isPropCauchyTailΠChoice : isProp CauchyTailΠChoice
isPropCauchyTailΠChoice =
  isPropΠ λ _ → isPropΠ λ _ → squash₁


cauchyTailΠChoice≃pointwiseCauchyChoice :
  CauchyTailΠChoice ≃ PointwiseCauchyChoice
cauchyTailΠChoice≃pointwiseCauchyChoice =
  propBiimpl→Equiv
    isPropCauchyTailΠChoice
    isPropPointwiseCauchyChoice
    cauchyTailΠChoice→pointwiseCauchyChoice
    pointwiseCauchyChoice→cauchyTailΠChoice


pointwiseCentered→cauchyContinuous :
  PointwiseCauchyChoice →
  ∀ {f : M → T.ℭ̂ₛ} →
  IsPointwiseCompletionCenteredContinuous f →
  C.IsCauchyContinuous f
pointwiseCentered→cauchyContinuous choice {f} pointwise =
  pointwiseCentered→cauchyContinuousWithGraphChoice pointwise
    (λ _ y _ _ → choice y)


liftPointwiseCompletionCentered :
  PointwiseCauchyChoice →
  (f : M → T.ℭ̂ₛ) →
  IsPointwiseCompletionCenteredContinuous f →
  S.ℭ̂ₛ → T.ℭ̂ₛ
liftPointwiseCompletionCentered choice f pointwise =
  C.liftCauchyContinuous f
    (pointwiseCentered→cauchyContinuous choice pointwise)


liftPointwiseCompletionCentered-ι :
  ∀ choice f pointwise q →
  liftPointwiseCompletionCentered choice f pointwise (S.ι q) ≡ f q
liftPointwiseCompletionCentered-ι choice f pointwise =
  C.liftCauchyContinuous-ι f
    (pointwiseCentered→cauchyContinuous choice pointwise)


liftPointwiseCompletionCentered-isContinuous :
  ∀ choice f pointwise →
  isContinuous
    (SP.ℭ̂ₛPremetricSpace .snd)
    (liftPointwiseCompletionCentered choice f pointwise)
    (TP.ℭ̂ₛPremetricSpace .snd)
liftPointwiseCompletionCentered-isContinuous choice f pointwise =
  liftCauchyContinuous-isContinuous f
    (pointwiseCentered→cauchyContinuous choice pointwise)
    pointwise
