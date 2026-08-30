open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.CauchySequence.Extension.CompletionCentered
  {ℓM} {ℓM'} {ℓN} {ℓN'}
  (M' : PremetricSpace ℓM ℓM')
  (N' : PremetricSpace ℓN ℓN') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels hiding (extend)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.Properties

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Base hiding (isProp∼)
import Cubical.Data.Rationals.Properties as ℚ
open import Cubical.Data.Rationals.Order as ℚ
  renaming (_<_ to _<ℚ_ ; _≤_ to _≤ℚ_)

open import Cubical.Relation.Premetric.Mappings

import Cubical.Relation.Premetric.Completion.CauchySequence.Base
  as CauchyCompletion
import Cubical.Relation.Premetric.Completion.CauchySequence.Premetric
  as CompletionPremetric
import Cubical.Relation.Premetric.Completion.CauchySequence.Extension.CauchyGraph
  as CauchyGraphDefinition

module S = CauchyCompletion M'
module SP = CompletionPremetric M'
module T = CauchyCompletion N'
module TP = CompletionPremetric N'
module G = CauchyGraphDefinition M' N'

private
  M = M' .fst
  ℓₘ = ℓ-max (ℓ-max ℓM ℓM') (ℓ-max ℓN ℓN')

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ
open OrderedCommRingStr (snd ℚOrderedCommRing)
open OrderedCommRingTheory ℚOrderedCommRing
open OrderedCommRingReasoning ℚOrderedCommRing


-- The radius is chosen merely and separately for every output radius.
-- This order of Π and propositional truncation matches ordinary pointwise
-- continuity and the radiuswise Cauchy witness used by this completion.

CenteredRadiusFor :
  (M → T.Completion) → S.Completion → ℚ₊ → Type ℓₘ
CenteredRadiusFor f x ε =
  Σ[ δ ∈ ℚ₊ ]
    (∀ q r →
      S.ι q S.≈ᶜ[ δ ] x →
      S.ι r S.≈ᶜ[ δ ] x →
      f q T.≈ᶜ[ ε ] f r)


record IsCompletionCenteredContinuous
  (f : M → T.Completion) : Type ℓₘ where
  no-eta-equality
  field
    at : ∀ x ε → ∥ CenteredRadiusFor f x ε ∥₁

open IsCompletionCenteredContinuous


isPropIsCompletionCenteredContinuous : ∀ f →
  isProp (IsCompletionCenteredContinuous f)
isPropIsCompletionCenteredContinuous f a b i .at x ε =
  squash₁ (a .at x ε) (b .at x ε) i


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


-- Ordinary continuity gives centered continuity of the dense restriction.

continuous→completionCenteredRestriction :
  ∀ (F : S.Completion → T.Completion) →
  isContinuous
    (SP.CompletionPremetricSpace .snd) F
    (TP.CompletionPremetricSpace .snd) →
  IsCompletionCenteredContinuous (F ∘ S.ι)
continuous→completionCenteredRestriction F F-cont .at x ε =
  PT.map withRadius
    (F-cont x .IsContinuousAt.pres≈ (ε /2₊))
  where
  withRadius :
    (Σ[ δ ∈ ℚ₊ ]
      (∀ y → x S.≈ᶜ[ δ ] y →
        F x T.≈ᶜ[ ε /2₊ ] F y)) →
    CenteredRadiusFor (F ∘ S.ι) x ε
  withRadius (δ , preserve) = δ , λ q r ιq≈x ιr≈x →
    subst (F (S.ι q) T.≈ᶜ[_] F (S.ι r))
      (ℚ₊≡ (/2+/2≡id (fst ε)))
      (TP.tri≈ᶜ (F (S.ι q)) (F x) (F (S.ι r))
        (ε /2₊) (ε /2₊)
        (T.sym≈ᶜ (F x) (F (S.ι q)) (ε /2₊)
          (preserve (S.ι q)
            (S.sym≈ᶜ (S.ι q) x δ ιq≈x)))
        (preserve (S.ι r)
          (S.sym≈ᶜ (S.ι r) x δ ιr≈x)))


-- Because IsCauchySequence truncates a tail separately at each radius,
-- centered continuity directly supplies the graph-preservation hypothesis.

completionCenteredContinuous→preservesCauchyGraphs :
  ∀ {f : M → T.Completion} →
  IsCompletionCenteredContinuous f →
  G.PreservesCauchyGraphs f
completionCenteredContinuous→preservesCauchyGraphs {f} centered =
  G.preservesCauchyGraphs preserve
  where
  preserve : ∀ x y →
    (∀ n → G.GraphClosure f (x n) (y n)) →
    S.IsCauchySequence x → T.IsCauchySequence y
  preserve x y joint gx ε =
    PT.rec squash₁ withRadius
      (centered .at (S.lim x gx) outputRadius)
    where
    outputRadius = ε /4₊

    withRadius :
      CenteredRadiusFor f (S.lim x gx) outputRadius →
      ∥ T.CauchyTail y ε ∥₁
    withRadius (centerRadius , local) =
      PT.map withSource (gx sourceRadius)
      where
      sourceRadius = centerRadius /4₊

      step :
        (N : ℕ) →
        (∀ m n → N ℕ.≤ m → N ℕ.≤ n →
          x m S.≈ᶜ[ sourceRadius ] x n) →
        ∀ m n → N ℕ.≤ m → N ℕ.≤ n →
        (Σ[ q ∈ M ]
          (S.ι q S.≈ᶜ[ sourceRadius ] x m) ×
          (f q T.≈ᶜ[ outputRadius ] y m)) →
        (Σ[ r ∈ M ]
          (S.ι r S.≈ᶜ[ sourceRadius ] x n) ×
          (f r T.≈ᶜ[ outputRadius ] y n)) →
        y m T.≈ᶜ[ ε ] y n
      step N xc m n N≤m N≤n
        (q , ιq≈xm , fq≈ym) (r , ιr≈xn , fr≈yn) =
        T.isMonotone≈ᶜ< (y m) (y n) _ ε (tripleQuarter< ε)
          (TP.tri≈ᶜ (y m) (f r) (y n)
            (outputRadius +₊ outputRadius) outputRadius
            (TP.tri≈ᶜ (y m) (f q) (f r)
              outputRadius outputRadius
              (T.sym≈ᶜ (f q) (y m) outputRadius fq≈ym)
              (local q r ιq≈center ιr≈center))
            fr≈yn)
        where
        ιq≈center : S.ι q S.≈ᶜ[ centerRadius ] S.lim x gx
        ιq≈center = SP.ι-close-lim-from-late
          q x gx centerRadius N xc m N≤m ιq≈xm

        ιr≈center : S.ι r S.≈ᶜ[ centerRadius ] S.lim x gx
        ιr≈center = SP.ι-close-lim-from-late
          r x gx centerRadius N xc n N≤n ιr≈xn

      withSource : S.CauchyTail x sourceRadius → T.CauchyTail y ε
      withSource (N , xc) = N , λ m n N≤m N≤n →
        PT.rec2 (T.isProp≈ᶜ (y m) ε (y n))
          (step N xc m n N≤m N≤n)
          (joint m sourceRadius outputRadius)
          (joint n sourceRadius outputRadius)


-- A total closed graph with a centered dense restriction is continuous.

graphExtension-isContinuous :
  ∀ (f : M → T.Completion) (F : S.Completion → T.Completion) →
  IsCompletionCenteredContinuous f →
  (∀ x → G.GraphClosure f x (F x)) →
  isContinuous
    (SP.CompletionPremetricSpace .snd) F
    (TP.CompletionPremetricSpace .snd)
graphExtension-isContinuous f F centered graph x
  .IsContinuousAt.pres≈ ε =
  PT.map withRadius (centered .at x outputRadius)
  where
  outputRadius = ε /4₊

  withRadius :
    CenteredRadiusFor f x outputRadius →
    Σ[ δ ∈ ℚ₊ ]
      (∀ y → x S.≈ᶜ[ δ ] y → F x T.≈ᶜ[ ε ] F y)
  withRadius (centerRadius , local) =
    sourceRadius , preserve
    where
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
      x S.≈ᶜ[ sourceRadius ] y → F x T.≈ᶜ[ ε ] F y
    preserve y x≈y =
      PT.rec2 (T.isProp≈ᶜ (F x) ε (F y)) step
        (graph x sourceRadius outputRadius)
        (graph y sourceRadius outputRadius)
      where
      step :
        (Σ[ q ∈ M ]
          (S.ι q S.≈ᶜ[ sourceRadius ] x) ×
          (f q T.≈ᶜ[ outputRadius ] F x)) →
        (Σ[ r ∈ M ]
          (S.ι r S.≈ᶜ[ sourceRadius ] y) ×
          (f r T.≈ᶜ[ outputRadius ] F y)) →
        F x T.≈ᶜ[ ε ] F y
      step (q , ιq≈x , fq≈Fx) (r , ιr≈y , fr≈Fy) =
        T.isMonotone≈ᶜ< (F x) (F y) _ ε (tripleQuarter< ε)
          (TP.tri≈ᶜ (F x) (f r) (F y)
            (outputRadius +₊ outputRadius) outputRadius
            (TP.tri≈ᶜ (F x) (f q) (f r)
              outputRadius outputRadius
              (T.sym≈ᶜ (f q) (F x) outputRadius fq≈Fx)
              (local q r
                (S.isMonotone≈ᶜ< (S.ι q) x
                  sourceRadius centerRadius source<Center ιq≈x)
                (S.isMonotone≈ᶜ< (S.ι r) x
                  (sourceRadius +₊ sourceRadius) centerRadius
                  twiceSource<Center
                  (SP.tri≈ᶜ (S.ι r) y x
                    sourceRadius sourceRadius
                    ιr≈y
                    (S.sym≈ᶜ x y sourceRadius x≈y)))))
            fr≈Fy)


-- Continuous maps lie in the closure of the graph of their restriction.

continuousRestriction-graph :
  ∀ (F : S.Completion → T.Completion) →
  isContinuous
    (SP.CompletionPremetricSpace .snd) F
    (TP.CompletionPremetricSpace .snd) →
  ∀ x → G.GraphClosure (F ∘ S.ι) x (F x)
continuousRestriction-graph F F-cont x α β =
  PT.rec squash₁ withRadius
    (F-cont x .IsContinuousAt.pres≈ β)
  where
  withRadius :
    (Σ[ δ ∈ ℚ₊ ]
      (∀ z → x S.≈ᶜ[ δ ] z → F x T.≈ᶜ[ β ] F z)) →
    ∃[ q ∈ M ]
      (S.ι q S.≈ᶜ[ α ] x) ×
      (F (S.ι q) T.≈ᶜ[ β ] F x)
  withRadius (δ , preserve) =
    PT.map withApproximation
      (SP.∃approx x (min₊ α δ /2₊))
    where
    sourceRadius = min₊ α δ /2₊

    withApproximation :
      (Σ[ q ∈ M ] (S.ι q S.≈ᶜ[ sourceRadius ] x)) →
      Σ[ q ∈ M ]
        (S.ι q S.≈ᶜ[ α ] x) ×
        (F (S.ι q) T.≈ᶜ[ β ] F x)
    withApproximation (q , ιq≈x) = q ,
      S.isMonotone≈ᶜ< (S.ι q) x sourceRadius α
        (min/2₊<L α δ) ιq≈x ,
      T.sym≈ᶜ (F x) (F (S.ι q)) β
        (preserve (S.ι q)
          (S.isMonotone≈ᶜ< x (S.ι q) sourceRadius δ
            (min/2₊<R α δ)
            (S.sym≈ᶜ (S.ι q) x sourceRadius ιq≈x)))


-- Density plus continuity determines a completed map by its base values.

continuousMap-ext :
  ∀ (F F' : S.Completion → T.Completion) →
  isContinuous
    (SP.CompletionPremetricSpace .snd) F
    (TP.CompletionPremetricSpace .snd) →
  isContinuous
    (SP.CompletionPremetricSpace .snd) F'
    (TP.CompletionPremetricSpace .snd) →
  (∀ q → F (S.ι q) ≡ F' (S.ι q)) →
  F ≡ F'
continuousMap-ext F F' F-cont F'-cont agree =
  funExt λ x →
    G.graphClosureUnique (F ∘ S.ι) restriction-preserves
      x (F x) (F' x)
      (continuousRestriction-graph F F-cont x)
      (subst (λ h → G.GraphClosure h x (F' x))
        (sym (funExt agree))
        (continuousRestriction-graph F' F'-cont x))
  where
  restriction-centered :
    IsCompletionCenteredContinuous (F ∘ S.ι)
  restriction-centered =
    continuous→completionCenteredRestriction F F-cont

  restriction-preserves : G.PreservesCauchyGraphs (F ∘ S.ι)
  restriction-preserves =
    completionCenteredContinuous→preservesCauchyGraphs
      restriction-centered


-- Canonical extension and its computation, graph, and continuity laws.

extendCompletionCentered :
  (f : M → T.Completion) →
  IsCompletionCenteredContinuous f →
  S.Completion → T.Completion
extendCompletionCentered f centered =
  G.extend f
    (completionCenteredContinuous→preservesCauchyGraphs centered)

extendCompletionCentered-graph :
  ∀ f centered x →
  G.GraphClosure f x (extendCompletionCentered f centered x)
extendCompletionCentered-graph f centered =
  G.extend-graph f
    (completionCenteredContinuous→preservesCauchyGraphs centered)

extendCompletionCentered-ι :
  ∀ f centered q →
  extendCompletionCentered f centered (S.ι q) ≡ f q
extendCompletionCentered-ι f centered =
  G.extend-ι f
    (completionCenteredContinuous→preservesCauchyGraphs centered)

extendCompletionCentered-lim :
  ∀ f centered x gx →
  extendCompletionCentered f centered (S.lim x gx) ≡
    T.lim (extendCompletionCentered f centered ∘ x) _
extendCompletionCentered-lim f centered =
  G.extend-lim f
    (completionCenteredContinuous→preservesCauchyGraphs centered)

extendCompletionCentered-presCauchy :
  ∀ f centered →
  G.PreservesCauchySequences (extendCompletionCentered f centered)
extendCompletionCentered-presCauchy f centered =
  G.extend-presCauchy f
    (completionCenteredContinuous→preservesCauchyGraphs centered)

extendCompletionCentered-isContinuous :
  ∀ f centered →
  isContinuous
    (SP.CompletionPremetricSpace .snd)
    (extendCompletionCentered f centered)
    (TP.CompletionPremetricSpace .snd)
extendCompletionCentered-isContinuous f centered =
  graphExtension-isContinuous f
    (extendCompletionCentered f centered) centered
    (extendCompletionCentered-graph f centered)

extendCompletionCentered-hypothesis-independent :
  ∀ f (centered centered' : IsCompletionCenteredContinuous f) →
  extendCompletionCentered f centered ≡
    extendCompletionCentered f centered'
extendCompletionCentered-hypothesis-independent f centered centered' =
  G.extend-hypothesis-independent f
    (completionCenteredContinuous→preservesCauchyGraphs centered)
    (completionCenteredContinuous→preservesCauchyGraphs centered')


-- Fiberwise classification by continuous extensions.

IsContinuousExtension :
  (M → T.Completion) →
  (S.Completion → T.Completion) → Type ℓₘ
IsContinuousExtension f F =
  isContinuous
    (SP.CompletionPremetricSpace .snd) F
    (TP.CompletionPremetricSpace .snd) ×
  (∀ q → F (S.ι q) ≡ f q)

isPropIsContinuousExtension : ∀ f F →
  isProp (IsContinuousExtension f F)
isPropIsContinuousExtension f F = isProp×
  (isPropIsContinuous
    (SP.CompletionPremetricSpace .snd) F
    (TP.CompletionPremetricSpace .snd))
  (isPropΠ λ _ → T.isSetCompletion _ _)

ContinuousExtension : (M → T.Completion) → Type ℓₘ
ContinuousExtension f =
  Σ[ F ∈ (S.Completion → T.Completion) ] IsContinuousExtension f F


continuousExtensionFunction-unique :
  ∀ f (E E' : ContinuousExtension f) → E .fst ≡ E' .fst
continuousExtensionFunction-unique f
  (F , F-cont , F-ι) (F' , F'-cont , F'-ι) =
  continuousMap-ext F F' F-cont F'-cont
    (λ q → F-ι q ∙ sym (F'-ι q))


isPropContinuousExtension : ∀ f → isProp (ContinuousExtension f)
isPropContinuousExtension f E E' =
  Σ≡Prop (isPropIsContinuousExtension f)
    (continuousExtensionFunction-unique f E E')


completionCentered→continuousExtension :
  ∀ f → IsCompletionCenteredContinuous f → ContinuousExtension f
completionCentered→continuousExtension f centered =
  extendCompletionCentered f centered ,
  extendCompletionCentered-isContinuous f centered ,
  extendCompletionCentered-ι f centered


continuousExtension→completionCentered :
  ∀ f → ContinuousExtension f → IsCompletionCenteredContinuous f
continuousExtension→completionCentered f (F , F-cont , F-ι) =
  subst IsCompletionCenteredContinuous
    (funExt F-ι)
    (continuous→completionCenteredRestriction F F-cont)


completionCenteredContinuous≃continuousExtension : ∀ f →
  IsCompletionCenteredContinuous f ≃ ContinuousExtension f
completionCenteredContinuous≃continuousExtension f =
  propBiimpl→Equiv
    (isPropIsCompletionCenteredContinuous f)
    (isPropContinuousExtension f)
    (completionCentered→continuousExtension f)
    (continuousExtension→completionCentered f)


-- Equivalently, restriction along ι is an equivalence between all
-- continuous maps of completions and all completion-centered base maps.

CompletionCenteredRestriction : Type ℓₘ
CompletionCenteredRestriction =
  Σ[ f ∈ (M → T.Completion) ] IsCompletionCenteredContinuous f

ContinuousMap : Type ℓₘ
ContinuousMap =
  Σ[ F ∈ (S.Completion → T.Completion) ]
    isContinuous
      (SP.CompletionPremetricSpace .snd) F
      (TP.CompletionPremetricSpace .snd)

RestrictionWithContinuousExtension : Type ℓₘ
RestrictionWithContinuousExtension =
  Σ[ f ∈ (M → T.Completion) ] ContinuousExtension f

completionCenteredRestrictionExtensionEquiv :
  CompletionCenteredRestriction ≃ RestrictionWithContinuousExtension
completionCenteredRestrictionExtensionEquiv =
  Σ-cong-equiv-snd completionCenteredContinuous≃continuousExtension

forgetRestriction : RestrictionWithContinuousExtension → ContinuousMap
forgetRestriction (_ , F , F-cont , _) = F , F-cont

attachRestriction : ContinuousMap → RestrictionWithContinuousExtension
attachRestriction (F , F-cont) =
  F ∘ S.ι , F , F-cont , λ _ → refl

restrictionWithContinuousExtensionMapIso :
  Iso RestrictionWithContinuousExtension ContinuousMap
restrictionWithContinuousExtensionMapIso .Iso.fun = forgetRestriction
restrictionWithContinuousExtensionMapIso .Iso.inv = attachRestriction
restrictionWithContinuousExtensionMapIso .Iso.sec _ = refl
restrictionWithContinuousExtensionMapIso .Iso.ret
  (f , F , F-cont , F-ι) =
  Σ≡Prop isPropContinuousExtension (funExt F-ι)

completionCenteredRestrictionContinuousMapEquiv :
  CompletionCenteredRestriction ≃ ContinuousMap
completionCenteredRestrictionContinuousMapEquiv =
  completionCenteredRestrictionExtensionEquiv
  ∙ₑ isoToEquiv restrictionWithContinuousExtensionMapIso
