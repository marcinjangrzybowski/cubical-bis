open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.CauchySequence.Extension.CauchyGraph
  {ℓM} {ℓM'} {ℓN} {ℓN'}
  (M' : PremetricSpace ℓM ℓM')
  (N' : PremetricSpace ℓN ℓN') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels hiding (extend)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open PositiveRationals
open PositiveHalvesℚ

import Cubical.Relation.Premetric.Completion.CauchySequence.Base
  as CauchyCompletion
import Cubical.Relation.Premetric.Completion.CauchySequence.Premetric
  as CompletionPremetric

module S = CauchyCompletion M'
module SP = CompletionPremetric M'
module T = CauchyCompletion N'
module TP = CompletionPremetric N'

private
  M = M' .fst
  N = N' .fst
  ℓₘ = ℓ-max (ℓ-max ℓM ℓM') (ℓ-max ℓN ℓN')


GraphClosure :
  (M → T.Completion) → S.Completion → T.Completion → Type ℓₘ
GraphClosure f x y = ∀ α β →
  ∃[ q ∈ M ]
    (S.ι q S.≈ᶜ[ α ] x) ×
    (f q T.≈ᶜ[ β ] y)

isPropGraphClosure : ∀ f x y →
  isProp (GraphClosure f x y)
isPropGraphClosure f x y =
  isPropΠ2 λ _ _ → squash₁


record PreservesCauchyGraphs (f : M → T.Completion) : Type ℓₘ where
  no-eta-equality
  pattern
  constructor preservesCauchyGraphs
  field
    presCauchyGraphs : ∀ (x : ℕ → S.Completion) (y : ℕ → T.Completion) →
      (∀ n → GraphClosure f (x n) (y n)) →
      S.IsCauchySequence x → T.IsCauchySequence y

open PreservesCauchyGraphs

isPropPreservesCauchyGraphs : ∀ f → isProp (PreservesCauchyGraphs f)
isPropPreservesCauchyGraphs f
  (preservesCauchyGraphs preserve)
  (preservesCauchyGraphs preserve') =
  cong preservesCauchyGraphs
    ((isPropΠ2 λ x y →
        isPropΠ λ _ →
        isPropΠ λ _ → T.isPropIsCauchySequence y)
      preserve preserve')


BaseGraphClosure :
  (M → N) → S.Completion → T.Completion → Type ℓₘ
BaseGraphClosure f = GraphClosure (T.ι ∘ f)

isPropBaseGraphClosure : ∀ f x y →
  isProp (BaseGraphClosure f x y)
isPropBaseGraphClosure f =
  isPropGraphClosure (T.ι ∘ f)

PreservesBaseCauchyGraphs : (M → N) → Type ℓₘ
PreservesBaseCauchyGraphs f = PreservesCauchyGraphs (T.ι ∘ f)

isPropPreservesBaseCauchyGraphs : ∀ f →
  isProp (PreservesBaseCauchyGraphs f)
isPropPreservesBaseCauchyGraphs f =
  isPropPreservesCauchyGraphs (T.ι ∘ f)


PreservesBaseCauchySequences : (M → T.Completion) → Type ℓₘ
PreservesBaseCauchySequences f =
  ∀ q → S.IsCauchySequence (S.ι ∘ q) → T.IsCauchySequence (f ∘ q)

preservesCauchyGraphs→preservesBaseSequences :
  ∀ {f} → PreservesCauchyGraphs f → PreservesBaseCauchySequences f
preservesCauchyGraphs→preservesBaseSequences {f} f-cc q =
  f-cc .presCauchyGraphs (S.ι ∘ q) (f ∘ q) exactGraph
  where
  exactGraph : ∀ n →
    GraphClosure f (S.ι (q n)) (f (q n))
  exactGraph n α β =
    ∣ q n , S.isRefl≈ᶜ (S.ι (q n)) α
          , T.isRefl≈ᶜ (f (q n)) β ∣₁


private
  alternate : T.Completion → T.Completion → ℕ → T.Completion
  alternate y y' zero = y
  alternate y y' (suc zero) = y'
  alternate y y' (suc (suc n)) = alternate y y' n

  alternate-even : ∀ y y' n →
    alternate y y' (ℕ.doubleℕ n) ≡ y
  alternate-even y y' zero = refl
  alternate-even y y' (suc n) = alternate-even y y' n

  alternate-odd : ∀ y y' n →
    alternate y y' (suc (ℕ.doubleℕ n)) ≡ y'
  alternate-odd y y' zero = refl
  alternate-odd y y' (suc n) = alternate-odd y y' n

  n≤double : ∀ n → n ℕ.≤ ℕ.doubleℕ n
  n≤double zero = ℕ.≤-refl
  n≤double (suc n) =
    ℕ.suc-≤-suc (ℕ.≤-trans (n≤double n) ℕ.≤-sucℕ)

  constantIsCauchySequence : ∀ x → S.IsCauchySequence (λ _ → x)
  constantIsCauchySequence x ε =
    ∣ zero , (λ m n _ _ → S.isRefl≈ᶜ x ε) ∣₁


graphClosureUnique : ∀ (f : M → T.Completion) →
  PreservesCauchyGraphs f →
  ∀ x y y' →
  GraphClosure f x y →
  GraphClosure f x y' →
  y ≡ y'
graphClosureUnique f f-cc x y y' xy xy' =
  T.eqCompletion y y' close
  where
  alternatingJoint : ∀ n →
    GraphClosure f x (alternate y y' n)
  alternatingJoint zero = xy
  alternatingJoint (suc zero) = xy'
  alternatingJoint (suc (suc n)) = alternatingJoint n

  alternatingWitness : T.IsCauchySequence (alternate y y')
  alternatingWitness = f-cc .presCauchyGraphs
    (λ _ → x) (alternate y y') alternatingJoint
    (constantIsCauchySequence x)

  close : ∀ ε → y T.≈ᶜ[ ε ] y'
  close ε =
    PT.rec (T.isProp≈ᶜ y ε y') withTail (alternatingWitness ε)
    where
    withTail : T.CauchyTail (alternate y y') ε →
      y T.≈ᶜ[ ε ] y'
    withTail (N , yc) =
      subst2 (T._≈ᶜ[ ε ]_)
        (alternate-even y y' N)
        (alternate-odd y y' N)
        (yc (ℕ.doubleℕ N) (suc (ℕ.doubleℕ N))
          (n≤double N)
          (ℕ.≤-trans (n≤double N) ℕ.≤-sucℕ))


ExtensionFiber : (M → T.Completion) → S.Completion → Type ℓₘ
ExtensionFiber f x = Σ[ y ∈ T.Completion ] GraphClosure f x y

isPropExtensionFiber : ∀ (f : M → T.Completion) →
  PreservesCauchyGraphs f →
  ∀ x → isProp (ExtensionFiber f x)
isPropExtensionFiber f f-cc x (y , xy) (y' , xy') =
  Σ≡Prop (isPropGraphClosure f x)
    (graphClosureUnique f f-cc x y y' xy xy')


private
  baseFiber : ∀ f q → ExtensionFiber f (S.ι q)
  baseFiber f q .fst = f q
  baseFiber f q .snd α β =
    ∣ q , S.isRefl≈ᶜ (S.ι q) α
        , T.isRefl≈ᶜ (f q) β ∣₁


  limitGraphClosure : ∀ f x gx y gy →
    (∀ n → GraphClosure f (x n) (y n)) →
    GraphClosure f (S.lim x gx) (T.lim y gy)
  limitGraphClosure f x gx y gy joint α β =
    PT.rec squash₁ withSource (gx (α /4₊))
    where
    targetRequired = (β /4₊) /4₊

    withSource : S.CauchyTail x (α /4₊) →
      ∃[ q ∈ M ]
        (S.ι q S.≈ᶜ[ α ] S.lim x gx) ×
        (f q T.≈ᶜ[ β ] T.lim y gy)
    withSource (N , xc) =
      PT.rec squash₁ (withTarget N xc) (gy targetRequired)
      where
      withTarget :
        (N : ℕ) →
        (∀ m n → N ℕ.≤ m → N ℕ.≤ n →
          x m S.≈ᶜ[ α /4₊ ] x n) →
        T.CauchyTail y targetRequired →
        ∃[ q ∈ M ]
          (S.ι q S.≈ᶜ[ α ] S.lim x gx) ×
          (f q T.≈ᶜ[ β ] T.lim y gy)
      withTarget N xc (K , yc) =
        PT.map makeLateApproximation
          (joint n (α /4₊) targetSmall)
        where
        targetSmall = targetRequired /4₊
        n = ℕ.max N K

        makeLateApproximation :
          (Σ[ q ∈ M ]
            (S.ι q S.≈ᶜ[ α /4₊ ] x n) ×
            (f q T.≈ᶜ[ targetSmall ] y n)) →
          Σ[ q ∈ M ]
            (S.ι q S.≈ᶜ[ α ] S.lim x gx) ×
            (f q T.≈ᶜ[ β ] T.lim y gy)
        makeLateApproximation (q , ιq∼xn , fq∼yn) = q ,
          SP.ι-close-lim-from-late q x gx α N xc n
            (ℕ.left-≤-max {m = N} {n = K}) ιq∼xn ,
          TP.close-lim-from-late (f q) y gy β K yc n
            (ℕ.right-≤-max {n = K} {m = N}) fq∼yn


  limitFiber : ∀ (f : M → T.Completion)
    (f-cc : PreservesCauchyGraphs f)
    (x : ℕ → S.Completion) (gx : S.IsCauchySequence x) →
    (∀ n → ExtensionFiber f (x n)) →
    ExtensionFiber f (S.lim x gx)
  limitFiber f f-cc x gx IH =
    T.lim y gy , limitGraphClosure f x gx y gy joint
    where
    y : ℕ → T.Completion
    y n = IH n .fst

    joint : ∀ n → GraphClosure f (x n) (y n)
    joint n = IH n .snd

    gy : T.IsCauchySequence y
    gy = f-cc .presCauchyGraphs x y joint gx


  fiberElim : ∀ (f : M → T.Completion)
    (f-cc : PreservesCauchyGraphs f) →
    S.ElimCompletion-Prop (ExtensionFiber f)
  fiberElim f f-cc .S.ElimCompletion-Prop.ιA = baseFiber f
  fiberElim f f-cc .S.ElimCompletion-Prop.limA = limitFiber f f-cc
  fiberElim f f-cc .S.ElimCompletion-Prop.isPropA =
    isPropExtensionFiber f f-cc


extensionFiber : ∀ (f : M → T.Completion) →
  PreservesCauchyGraphs f →
  ∀ x → ExtensionFiber f x
extensionFiber f f-cc = S.ElimCompletion-Prop.go (fiberElim f f-cc)

extend :
  (f : M → T.Completion) →
  PreservesCauchyGraphs f →
  S.Completion → T.Completion
extend f f-cc x = extensionFiber f f-cc x .fst

extend-graph :
  ∀ (f : M → T.Completion) (f-cc : PreservesCauchyGraphs f) x →
  GraphClosure f x (extend f f-cc x)
extend-graph f f-cc x = extensionFiber f f-cc x .snd

extend-ι :
  ∀ (f : M → T.Completion) (f-cc : PreservesCauchyGraphs f) q →
  extend f f-cc (S.ι q) ≡ f q
extend-ι f f-cc q = refl

extend-lim :
  ∀ (f : M → T.Completion) (f-cc : PreservesCauchyGraphs f) x gx →
  extend f f-cc (S.lim x gx) ≡
    T.lim (extend f f-cc ∘ x) _
extend-lim f f-cc x gx = refl

extend-unique :
  ∀ (f : M → T.Completion) (f-cc : PreservesCauchyGraphs f)
    (G : S.Completion → T.Completion) →
  (∀ x → GraphClosure f x (G x)) →
  extend f f-cc ≡ G
extend-unique f f-cc G G-joint =
  funExt λ x → graphClosureUnique f f-cc x _ _
    (extend-graph f f-cc x)
    (G-joint x)

extend-hypothesis-independent :
  ∀ (f : M → T.Completion)
    (f-cc f-cc' : PreservesCauchyGraphs f) →
  extend f f-cc ≡
    extend f f-cc'
extend-hypothesis-independent f f-cc f-cc' =
  extend-unique f f-cc
    (extend f f-cc')
    (extend-graph f f-cc')

extend-ext :
  ∀ (f g : M → T.Completion)
    (f-cc : PreservesCauchyGraphs f)
    (g-cc : PreservesCauchyGraphs g) →
  (∀ q → f q ≡ g q) →
  extend f f-cc ≡
    extend g g-cc
extend-ext f g f-cc g-cc f∼g =
  lift-cong f f-cc (funExt f∼g) g-cc
  where
  lift-cong :
    ∀ (f : M → T.Completion)
      (f-cc : PreservesCauchyGraphs f)
      {g : M → T.Completion} → f ≡ g →
      (g-cc : PreservesCauchyGraphs g) →
    extend f f-cc ≡
      extend g g-cc
  lift-cong f f-cc {g} f≡g =
    J (λ g _ → (g-cc : PreservesCauchyGraphs g) →
        extend f f-cc ≡
          extend g g-cc)
      (extend-hypothesis-independent f f-cc)
      f≡g

PreservesCauchySequences :
  (S.Completion → T.Completion) → Type ℓₘ
PreservesCauchySequences F =
  ∀ x → S.IsCauchySequence x → T.IsCauchySequence (F ∘ x)

extend-presCauchy :
  ∀ (f : M → T.Completion) (f-cc : PreservesCauchyGraphs f) →
  PreservesCauchySequences (extend f f-cc)
extend-presCauchy f f-cc x =
  f-cc .presCauchyGraphs x (F ∘ x)
    (λ n → extend-graph f f-cc (x n))
  where
  F = extend f f-cc


extendBase :
  (f : M → N) →
  PreservesBaseCauchyGraphs f →
  S.Completion → T.Completion
extendBase f =
  extend (T.ι ∘ f)

extendBase-graph :
  ∀ (f : M → N) (f-cc : PreservesBaseCauchyGraphs f) x →
  BaseGraphClosure f x
    (extendBase f f-cc x)
extendBase-graph f =
  extend-graph (T.ι ∘ f)

extendBase-ι :
  ∀ (f : M → N) (f-cc : PreservesBaseCauchyGraphs f) q →
  extendBase f f-cc (S.ι q) ≡ T.ι (f q)
extendBase-ι f =
  extend-ι (T.ι ∘ f)

extendBase-presCauchy :
  ∀ (f : M → N) (f-cc : PreservesBaseCauchyGraphs f) →
  PreservesCauchySequences
    (extendBase f f-cc)
extendBase-presCauchy f =
  extend-presCauchy (T.ι ∘ f)

extendBase-hypothesis-independent :
  ∀ (f : M → N)
    (f-cc f-cc' : PreservesBaseCauchyGraphs f) →
  extendBase f f-cc ≡
    extendBase f f-cc'
extendBase-hypothesis-independent f =
  extend-hypothesis-independent (T.ι ∘ f)

extendBase-ext :
  ∀ (f g : M → N)
    (f-cc : PreservesBaseCauchyGraphs f)
    (g-cc : PreservesBaseCauchyGraphs g) →
  (∀ q → f q ≡ g q) →
  extendBase f f-cc ≡
    extendBase g g-cc
extendBase-ext f g f-cc g-cc f∼g =
  extend-ext (T.ι ∘ f) (T.ι ∘ g)
    f-cc g-cc (λ q → cong T.ι (f∼g q))


CauchyGraphRestriction : Type ℓₘ
CauchyGraphRestriction =
  Σ[ f ∈ (M → T.Completion) ] PreservesCauchyGraphs f

PreservesCauchyGraphsExtension :
  (S.Completion → T.Completion) → Type ℓₘ
PreservesCauchyGraphsExtension F =
  PreservesCauchyGraphs (F ∘ S.ι) ×
  (∀ x → GraphClosure (F ∘ S.ι) x (F x))

isPropPreservesCauchyGraphsExtension : ∀ F →
  isProp (PreservesCauchyGraphsExtension F)
isPropPreservesCauchyGraphsExtension F = isProp×
  (isPropPreservesCauchyGraphs (F ∘ S.ι))
  (isPropΠ λ x →
    isPropGraphClosure (F ∘ S.ι) x (F x))

CauchyGraphExtension : Type ℓₘ
CauchyGraphExtension =
  Σ[ F ∈ (S.Completion → T.Completion) ] PreservesCauchyGraphsExtension F

extendRestriction :
  CauchyGraphRestriction → CauchyGraphExtension
extendRestriction (f , f-cc) =
  extend f f-cc ,
  f-cc , extend-graph f f-cc

restrictExtension :
  CauchyGraphExtension → CauchyGraphRestriction
restrictExtension (F , F-cc , _) = F ∘ S.ι , F-cc

preservesCauchyGraphsExtension-presCauchy :
  ∀ (F : S.Completion → T.Completion) →
  PreservesCauchyGraphsExtension F →
  PreservesCauchySequences F
preservesCauchyGraphsExtension-presCauchy F
  (restriction-cc , graph) x =
  restriction-cc .presCauchyGraphs x (F ∘ x)
    (λ n → graph (x n))

preservesCauchyGraphsRestrictionExtensionIso :
  Iso CauchyGraphRestriction CauchyGraphExtension
preservesCauchyGraphsRestrictionExtensionIso .Iso.fun =
  extendRestriction
preservesCauchyGraphsRestrictionExtensionIso .Iso.inv =
  restrictExtension
preservesCauchyGraphsRestrictionExtensionIso .Iso.sec
  (F , restriction-cc , graph) =
  Σ≡Prop isPropPreservesCauchyGraphsExtension
    (extend-unique
      (F ∘ S.ι) restriction-cc F graph)
preservesCauchyGraphsRestrictionExtensionIso .Iso.ret (f , f-cc) =
  Σ≡Prop isPropPreservesCauchyGraphs
    (funExt (extend-ι f f-cc))

preservesCauchyGraphsRestrictionExtensionEquiv :
  CauchyGraphRestriction ≃ CauchyGraphExtension
preservesCauchyGraphsRestrictionExtensionEquiv =
  isoToEquiv preservesCauchyGraphsRestrictionExtensionIso
