open import Cubical.Relation.Premetric.Base

module Cubical.Relation.Premetric.Completion.Alternative.Sequential.Lift.CauchyContinuous
  {ℓM} {ℓM'} {ℓN} {ℓN'}
  (M' : PremetricSpace ℓM ℓM')
  (N' : PremetricSpace ℓN ℓN') where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Nat as ℕ
open import Cubical.Data.Nat.Order as ℕ
open import Cubical.Data.Sigma

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.OrderedCommRing
open import Cubical.Algebra.OrderedCommRing.Instances.Rationals

open import Cubical.Data.Rationals.Base hiding (isProp∼)
open import Cubical.Data.Rationals.Order as ℚ
  renaming (_<_ to _<ℚ_ ; _≤_ to _≤ℚ_)
import Cubical.Data.Rationals.Properties as ℚ

import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Base
  as SequentialDefinition
import Cubical.Relation.Premetric.Completion.Alternative.Sequential.Properties
  as SequentialPropertiesDefinition

module S = SequentialDefinition M'
module SP = SequentialPropertiesDefinition M'
module T = SequentialDefinition N'
module TP = SequentialPropertiesDefinition N'

private
  M = M' .fst
  N = N' .fst
  ℓₘ = ℓ-max (ℓ-max ℓM ℓM') (ℓ-max ℓN ℓN')

open PositiveRationals
open PositiveHalvesℚ
open 1/2∈ℚ
open OrderedCommRingStr (snd ℚOrderedCommRing)
open OrderedCommRingReasoning ℚOrderedCommRing
open OrderedCommRingTheory ℚOrderedCommRing


JointlyApproximableFor :
  (M → T.ℭ̂ₛ) → S.ℭ̂ₛ → T.ℭ̂ₛ → Type ℓₘ
JointlyApproximableFor f x y = ∀ α β →
  ∃[ q ∈ M ]
    (S.ι q S.∼̂ₛ[ α ] x) ×
    (f q T.∼̂ₛ[ β ] y)

isPropJointlyApproximableFor : ∀ f x y →
  isProp (JointlyApproximableFor f x y)
isPropJointlyApproximableFor f x y =
  isPropΠ2 λ _ _ → squash₁


record IsCauchyContinuous (f : M → T.ℭ̂ₛ) : Type ℓₘ where
  no-eta-equality
  pattern
  constructor cauchyContinuous
  field
    presCauchyGraph : ∀ (x : ℕ → S.ℭ̂ₛ) (y : ℕ → T.ℭ̂ₛ) →
      (∀ n → JointlyApproximableFor f (x n) (y n)) →
      S.SeqWitness x → T.SeqWitness y

open IsCauchyContinuous

isPropIsCauchyContinuous : ∀ f → isProp (IsCauchyContinuous f)
isPropIsCauchyContinuous f
  (cauchyContinuous preserve)
  (cauchyContinuous preserve') =
  cong cauchyContinuous
    ((isPropΠ2 λ x y →
        isPropΠ λ _ →
        isPropΠ λ _ → squash₁)
      preserve preserve')


-- Specialization to an ordinary map between the two base premetric spaces.
-- The general definition above already allows a completed codomain, so the
-- only extra operation needed here is the codomain injection.

BaseJointlyApproximableFor :
  (M → N) → S.ℭ̂ₛ → T.ℭ̂ₛ → Type ℓₘ
BaseJointlyApproximableFor f = JointlyApproximableFor (T.ι ∘ f)

isPropBaseJointlyApproximableFor : ∀ f x y →
  isProp (BaseJointlyApproximableFor f x y)
isPropBaseJointlyApproximableFor f =
  isPropJointlyApproximableFor (T.ι ∘ f)

IsCauchyContinuousBase : (M → N) → Type ℓₘ
IsCauchyContinuousBase f = IsCauchyContinuous (T.ι ∘ f)

isPropIsCauchyContinuousBase : ∀ f →
  isProp (IsCauchyContinuousBase f)
isPropIsCauchyContinuousBase f =
  isPropIsCauchyContinuous (T.ι ∘ f)


MapsBaseCauchySequences : (M → T.ℭ̂ₛ) → Type ℓₘ
MapsBaseCauchySequences f =
  ∀ q → S.SeqWitness (S.ι ∘ q) → T.SeqWitness (f ∘ q)

isCauchyContinuous→mapsBaseCauchySequences :
  ∀ {f} → IsCauchyContinuous f → MapsBaseCauchySequences f
isCauchyContinuous→mapsBaseCauchySequences {f} f-cc q =
  f-cc .presCauchyGraph (S.ι ∘ q) (f ∘ q) exactGraph
  where
  exactGraph : ∀ n →
    JointlyApproximableFor f (S.ι (q n)) (f (q n))
  exactGraph n α β =
    ∣ q n , S.isRefl∼̂ₛ (S.ι (q n)) α
          , T.isRefl∼̂ₛ (f (q n)) β ∣₁


-- Density upgrades the primitive injected-left-endpoint limit lemma to an
-- arbitrary endpoint.  The argument is independent of the base space.

close-lim-from-late :
  ∀ (z : T.ℭ̂ₛ) (y : ℕ → T.ℭ̂ₛ) (gy : T.SeqWitness y)
    (K : ℚ₊ → ℕ)
    (yc : ∀ ε m n → K ε ℕ.≤ m → K ε ℕ.≤ n →
      y m T.∼̂ₛ[ ε ] y n)
    ε n →
  K ((ε /4₊) /4₊) ℕ.≤ n →
  z T.∼̂ₛ[ (((ε /4₊) /4₊) /4₊) ] y n →
  z T.∼̂ₛ[ ε ] T.lim y gy
close-lim-from-late = TP.close-lim-from-late


private
  alternate : T.ℭ̂ₛ → T.ℭ̂ₛ → ℕ → T.ℭ̂ₛ
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

  constantSeqWitness : ∀ x → S.SeqWitness (λ _ → x)
  constantSeqWitness x =
    ∣ (λ _ → zero) ,
      (λ ε m n _ _ → S.isRefl∼̂ₛ x ε) ∣₁


jointlyApproximable-equal : ∀ (f : M → T.ℭ̂ₛ) →
  IsCauchyContinuous f →
  ∀ x y y' →
  JointlyApproximableFor f x y →
  JointlyApproximableFor f x y' →
  y ≡ y'
jointlyApproximable-equal f f-cc x y y' xy xy' =
  T.eqℭ y y' close
  where
  alternatingJoint : ∀ n →
    JointlyApproximableFor f x (alternate y y' n)
  alternatingJoint zero = xy
  alternatingJoint (suc zero) = xy'
  alternatingJoint (suc (suc n)) = alternatingJoint n

  alternatingWitness : T.SeqWitness (alternate y y')
  alternatingWitness = f-cc .presCauchyGraph
    (λ _ → x) (alternate y y') alternatingJoint
    (constantSeqWitness x)

  close : ∀ ε → y T.∼̂ₛ[ ε ] y'
  close ε = PT.rec (T.isProp∼ y ε y') withCauchy alternatingWitness
    where
    withCauchy : T.CauchySeq (alternate y y') → y T.∼̂ₛ[ ε ] y'
    withCauchy (N , yc) =
      subst2 (T._∼̂ₛ[ ε ]_)
        (alternate-even y y' (N ε))
        (alternate-odd y y' (N ε))
        (yc ε (ℕ.doubleℕ (N ε)) (suc (ℕ.doubleℕ (N ε)))
          (n≤double (N ε))
          (ℕ.≤-trans (n≤double (N ε)) ℕ.≤-sucℕ))


LiftFiber : (M → T.ℭ̂ₛ) → S.ℭ̂ₛ → Type ℓₘ
LiftFiber f x = Σ[ y ∈ T.ℭ̂ₛ ] JointlyApproximableFor f x y

isPropLiftFiber : ∀ (f : M → T.ℭ̂ₛ) →
  IsCauchyContinuous f →
  ∀ x → isProp (LiftFiber f x)
isPropLiftFiber f f-cc x (y , xy) (y' , xy') =
  Σ≡Prop (isPropJointlyApproximableFor f x)
    (jointlyApproximable-equal f f-cc x y y' xy xy')


private
  baseFiber : ∀ f q → LiftFiber f (S.ι q)
  baseFiber f q .fst = f q
  baseFiber f q .snd α β =
    ∣ q , S.isRefl∼̂ₛ (S.ι q) α
        , T.isRefl∼̂ₛ (f q) β ∣₁


  limitJointlyApproximable : ∀ f x gx y gy →
    (∀ n → JointlyApproximableFor f (x n) (y n)) →
    JointlyApproximableFor f (S.lim x gx) (T.lim y gy)
  limitJointlyApproximable f x gx y gy joint α β =
    PT.rec squash₁ withSource gx
    where
    withSource : S.CauchySeq x →
      ∃[ q ∈ M ]
        (S.ι q S.∼̂ₛ[ α ] S.lim x gx) ×
        (f q T.∼̂ₛ[ β ] T.lim y gy)
    withSource (N , xc) = PT.rec squash₁ (withTarget N xc) gy
      where
      withTarget :
        (N : ℚ₊ → ℕ) →
        (∀ ε m n → N ε ℕ.≤ m → N ε ℕ.≤ n →
          x m S.∼̂ₛ[ ε ] x n) →
        T.CauchySeq y →
        ∃[ q ∈ M ]
          (S.ι q S.∼̂ₛ[ α ] S.lim x gx) ×
          (f q T.∼̂ₛ[ β ] T.lim y gy)
      withTarget N xc (K , yc) =
        PT.map makeLateApproximation
          (joint n (α /4₊) targetSmall)
        where
        targetRequired = (β /4₊) /4₊
        targetSmall = targetRequired /4₊

        n : ℕ
        n = ℕ.max (N (α /4₊)) (K targetRequired)

        makeLateApproximation :
          (Σ[ q ∈ M ]
            (S.ι q S.∼̂ₛ[ α /4₊ ] x n) ×
            (f q T.∼̂ₛ[ targetSmall ] y n)) →
          Σ[ q ∈ M ]
            (S.ι q S.∼̂ₛ[ α ] S.lim x gx) ×
            (f q T.∼̂ₛ[ β ] T.lim y gy)
        makeLateApproximation (q , ιq∼xn , fq∼yn) = q ,
          SP.ι-close-lim-from-late q x gx N xc α n
            (ℕ.left-≤-max
              {m = N (α /4₊)} {n = K targetRequired}) ιq∼xn ,
          close-lim-from-late (f q) y gy K yc β n
            (ℕ.right-≤-max
              {n = K targetRequired} {m = N (α /4₊)}) fq∼yn


  limitFiber : ∀ (f : M → T.ℭ̂ₛ)
    (f-cc : IsCauchyContinuous f)
    (x : ℕ → S.ℭ̂ₛ) (gx : S.SeqWitness x) →
    (∀ n → LiftFiber f (x n)) →
    LiftFiber f (S.lim x gx)
  limitFiber f f-cc x gx IH =
    T.lim y gy , limitJointlyApproximable f x gx y gy joint
    where
    y : ℕ → T.ℭ̂ₛ
    y n = IH n .fst

    joint : ∀ n → JointlyApproximableFor f (x n) (y n)
    joint n = IH n .snd

    gy : T.SeqWitness y
    gy = f-cc .presCauchyGraph x y joint gx


  fiberElim : ∀ (f : M → T.ℭ̂ₛ)
    (f-cc : IsCauchyContinuous f) →
    S.Elimℭ̂ₛ-Prop (LiftFiber f)
  fiberElim f f-cc .S.Elimℭ̂ₛ-Prop.ιA = baseFiber f
  fiberElim f f-cc .S.Elimℭ̂ₛ-Prop.limA = limitFiber f f-cc
  fiberElim f f-cc .S.Elimℭ̂ₛ-Prop.isPropA =
    isPropLiftFiber f f-cc


liftFiber : ∀ (f : M → T.ℭ̂ₛ) →
  IsCauchyContinuous f →
  ∀ x → LiftFiber f x
liftFiber f f-cc = S.Elimℭ̂ₛ-Prop.go (fiberElim f f-cc)

liftCauchyContinuous :
  (f : M → T.ℭ̂ₛ) →
  IsCauchyContinuous f →
  S.ℭ̂ₛ → T.ℭ̂ₛ
liftCauchyContinuous f f-cc x = liftFiber f f-cc x .fst

liftCauchyContinuous-joint :
  ∀ (f : M → T.ℭ̂ₛ) (f-cc : IsCauchyContinuous f) x →
  JointlyApproximableFor f x (liftCauchyContinuous f f-cc x)
liftCauchyContinuous-joint f f-cc x = liftFiber f f-cc x .snd

liftCauchyContinuous-ι :
  ∀ (f : M → T.ℭ̂ₛ) (f-cc : IsCauchyContinuous f) q →
  liftCauchyContinuous f f-cc (S.ι q) ≡ f q
liftCauchyContinuous-ι f f-cc q = refl

liftCauchyContinuous-lim :
  ∀ (f : M → T.ℭ̂ₛ) (f-cc : IsCauchyContinuous f) x xs →
  liftCauchyContinuous f f-cc (S.lim x xs) ≡
    T.lim (liftCauchyContinuous f f-cc ∘ x) _
liftCauchyContinuous-lim f f-cc x xs = refl

MapsCompletionCauchySequences :
  (S.ℭ̂ₛ → T.ℭ̂ₛ) → Type ℓₘ
MapsCompletionCauchySequences F =
  ∀ x → S.SeqWitness x → T.SeqWitness (F ∘ x)

liftCauchyContinuous-presCauchy :
  ∀ (f : M → T.ℭ̂ₛ) (f-cc : IsCauchyContinuous f) →
  MapsCompletionCauchySequences (liftCauchyContinuous f f-cc)
liftCauchyContinuous-presCauchy f f-cc x =
  f-cc .presCauchyGraph x (F ∘ x)
    (λ n → liftCauchyContinuous-joint f f-cc (x n))
  where
  F = liftCauchyContinuous f f-cc


liftCauchyContinuous-unique :
  ∀ (f : M → T.ℭ̂ₛ) (f-cc : IsCauchyContinuous f)
    (G : S.ℭ̂ₛ → T.ℭ̂ₛ) →
    (∀ x → JointlyApproximableFor f x (G x)) →
    liftCauchyContinuous f f-cc ≡ G
liftCauchyContinuous-unique f f-cc G G-joint =
  funExt λ x → jointlyApproximable-equal f f-cc x _ _
    (liftCauchyContinuous-joint f f-cc x)
    (G-joint x)

liftCauchyContinuous-hypothesis-independent :
  ∀ (f : M → T.ℭ̂ₛ)
    (f-cc f-cc' : IsCauchyContinuous f) →
    liftCauchyContinuous f f-cc ≡
      liftCauchyContinuous f f-cc'
liftCauchyContinuous-hypothesis-independent f f-cc f-cc' =
  liftCauchyContinuous-unique f f-cc
    (liftCauchyContinuous f f-cc')
    (liftCauchyContinuous-joint f f-cc')

-- Extensionality compares both the base maps and their independently chosen
-- Cauchy-continuity witnesses.  The existing hypothesis-independence theorem
-- is exactly the reflexive case after function extensionality.

liftCauchyContinuous-ext :
  ∀ (f g : M → T.ℭ̂ₛ)
    (f-cc : IsCauchyContinuous f)
    (g-cc : IsCauchyContinuous g) →
  (∀ q → f q ≡ g q) →
  liftCauchyContinuous f f-cc ≡
    liftCauchyContinuous g g-cc
liftCauchyContinuous-ext f g f-cc g-cc f∼g =
  liftCauchyContinuous-cong f f-cc (funExt f∼g) g-cc
  where
  liftCauchyContinuous-cong :
    ∀ (f : M → T.ℭ̂ₛ)
      (f-cc : IsCauchyContinuous f)
      {g : M → T.ℭ̂ₛ} → f ≡ g →
      (g-cc : IsCauchyContinuous g) →
    liftCauchyContinuous f f-cc ≡
      liftCauchyContinuous g g-cc
  liftCauchyContinuous-cong f f-cc {g} f≡g =
    J (λ g _ → (g-cc : IsCauchyContinuous g) →
        liftCauchyContinuous f f-cc ≡
          liftCauchyContinuous g g-cc)
      (liftCauchyContinuous-hypothesis-independent f f-cc)
      f≡g


-- Completing both sides of a map between base premetric spaces.

liftCauchyContinuousBase :
  (f : M → N) →
  IsCauchyContinuousBase f →
  S.ℭ̂ₛ → T.ℭ̂ₛ
liftCauchyContinuousBase f =
  liftCauchyContinuous (T.ι ∘ f)

liftCauchyContinuousBase-joint :
  ∀ (f : M → N) (f-cc : IsCauchyContinuousBase f) x →
  BaseJointlyApproximableFor f x
    (liftCauchyContinuousBase f f-cc x)
liftCauchyContinuousBase-joint f =
  liftCauchyContinuous-joint (T.ι ∘ f)

liftCauchyContinuousBase-ι :
  ∀ (f : M → N) (f-cc : IsCauchyContinuousBase f) q →
  liftCauchyContinuousBase f f-cc (S.ι q) ≡ T.ι (f q)
liftCauchyContinuousBase-ι f =
  liftCauchyContinuous-ι (T.ι ∘ f)

liftCauchyContinuousBase-presCauchy :
  ∀ (f : M → N) (f-cc : IsCauchyContinuousBase f) →
  MapsCompletionCauchySequences (liftCauchyContinuousBase f f-cc)
liftCauchyContinuousBase-presCauchy f =
  liftCauchyContinuous-presCauchy (T.ι ∘ f)

liftCauchyContinuousBase-hypothesis-independent :
  ∀ (f : M → N)
    (f-cc f-cc' : IsCauchyContinuousBase f) →
    liftCauchyContinuousBase f f-cc ≡
      liftCauchyContinuousBase f f-cc'
liftCauchyContinuousBase-hypothesis-independent f =
  liftCauchyContinuous-hypothesis-independent (T.ι ∘ f)

liftCauchyContinuousBase-ext :
  ∀ (f g : M → N)
    (f-cc : IsCauchyContinuousBase f)
    (g-cc : IsCauchyContinuousBase g) →
  (∀ q → f q ≡ g q) →
  liftCauchyContinuousBase f f-cc ≡
    liftCauchyContinuousBase g g-cc
liftCauchyContinuousBase-ext f g f-cc g-cc f∼g =
  liftCauchyContinuous-ext (T.ι ∘ f) (T.ι ∘ g)
    f-cc g-cc (λ q → cong T.ι (f∼g q))


CauchyContinuousRestriction : Type ℓₘ
CauchyContinuousRestriction =
  Σ[ f ∈ (M → T.ℭ̂ₛ) ] IsCauchyContinuous f

IsCauchyContinuousExtension : (S.ℭ̂ₛ → T.ℭ̂ₛ) → Type ℓₘ
IsCauchyContinuousExtension F =
  IsCauchyContinuous (F ∘ S.ι) ×
  (∀ x → JointlyApproximableFor (F ∘ S.ι) x (F x))

isPropIsCauchyContinuousExtension : ∀ F →
  isProp (IsCauchyContinuousExtension F)
isPropIsCauchyContinuousExtension F = isProp×
  (isPropIsCauchyContinuous (F ∘ S.ι))
  (isPropΠ λ x →
    isPropJointlyApproximableFor (F ∘ S.ι) x (F x))

CauchyContinuousExtension : Type ℓₘ
CauchyContinuousExtension =
  Σ[ F ∈ (S.ℭ̂ₛ → T.ℭ̂ₛ) ]
    IsCauchyContinuousExtension F


extendCauchyContinuous :
  CauchyContinuousRestriction → CauchyContinuousExtension
extendCauchyContinuous (f , f-cc) =
  F , f-cc , liftCauchyContinuous-joint f f-cc
  where
  F = liftCauchyContinuous f f-cc

restrictCauchyContinuous :
  CauchyContinuousExtension → CauchyContinuousRestriction
restrictCauchyContinuous (F , F-cc , _) = F ∘ S.ι , F-cc

cauchyContinuousExtension-presCauchy :
  ∀ (F : S.ℭ̂ₛ → T.ℭ̂ₛ) →
  IsCauchyContinuousExtension F →
  MapsCompletionCauchySequences F
cauchyContinuousExtension-presCauchy F (restriction-cc , graph) x =
  restriction-cc .presCauchyGraph x (F ∘ x)
    (λ n → graph (x n))


cauchyContinuousRestrictionExtensionIso :
  Iso CauchyContinuousRestriction CauchyContinuousExtension
cauchyContinuousRestrictionExtensionIso .Iso.fun =
  extendCauchyContinuous
cauchyContinuousRestrictionExtensionIso .Iso.inv =
  restrictCauchyContinuous
cauchyContinuousRestrictionExtensionIso .Iso.sec
  (F , restriction-cc , graph) =
  Σ≡Prop isPropIsCauchyContinuousExtension
    (liftCauchyContinuous-unique
      (F ∘ S.ι) restriction-cc F graph)
cauchyContinuousRestrictionExtensionIso .Iso.ret (f , f-cc) =
  Σ≡Prop isPropIsCauchyContinuous
    (funExt (liftCauchyContinuous-ι f f-cc))

cauchyContinuousRestrictionExtensionEquiv :
  CauchyContinuousRestriction ≃ CauchyContinuousExtension
cauchyContinuousRestrictionExtensionEquiv =
  isoToEquiv cauchyContinuousRestrictionExtensionIso

